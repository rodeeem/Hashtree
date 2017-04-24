defmodule Hashtree do

  @moduledoc """
  This module generates MerkleRoot and MerklePath. And it also verifies data given in the argument.
  SHA256 is used for the hashing.
  """

  defp sha256(node) do
    :crypto.hash(:sha256, node)
    |> Base.encode16(case: :lower)
  end

  defp gen_parents([x |[y | tail]]) do
    [sha256(x <> y) | gen_parents(tail)]
  end

  defp gen_parents([]), do: []

  defp gen_parents([_]) do
    raise ArgumentError, message: "element counts need to be powers number of 2"
  end
  
  defp gen_full_nodes([top | []]), do: [top]

  defp gen_full_nodes(data) do
    [data | gen_full_nodes(gen_parents(data))]
  end

  defp gen_fullnodes(data) do
    data
    |> Enum.map(&sha256(&1))
    |> gen_full_nodes
  end

  defp gen_merkle_root([top | []]), do: top
  
  defp gen_merkle_root(data) do
    data
    |> gen_parents
    |> gen_merkle_root
  end

  @doc """
  Generate MerkleRoot. 
  
      iex(1)> ls = ["a", "b", "c", "d"]
      iex(2)> Hashtree.merkle_root(ls)
      "58c89d709329eb37285837b042ab6ff72c7c8f74de0446b091b6a0131c102cfd"
  """

  @spec merkle_root(list) :: String.t
  def merkle_root(data) do
    data
    |> Enum.map(&sha256(&1))
    |> gen_merkle_root
  end
    
  defp pow2(h), do: trunc(:math.pow(2, h))

  defp update_auth(at, auth, h, value) do
    List.replace_at(auth, h, {at, value})
  end
  
  defp next_stack(start, fullnodes, h) do
    fullnodes
    |> Enum.at(h)
    |> Enum.at(div(start, pow2(h)))
  end
    
  defp update_stack(stack, start, fullnodes, h) do
    require Integer
    if Integer.is_even(div(start, pow2(h))) do
      stack
      |> List.replace_at(h, {:left, next_stack(start, fullnodes, h)})
    else
      stack
      |> List.replace_at(h, {:right, next_stack(start, fullnodes, h)})
    end
  end
        
  defp auth_at_left(leaf, h), do: leaf + 1 + 2 * pow2(h)

  defp auth_at_right(leaf), do: leaf + 1

  defp update_both(auth, stack, fullnodes, leaf, h) do
    if rem(leaf + 1, pow2(h)) == 0 do
      {auth, stack} = case Enum.at(stack, h) do
			{:left, value} ->
			  {update_auth(:left, auth, h, value), update_stack(stack, auth_at_left(leaf, h), fullnodes, h)}
			{:right, value} ->
			  {update_auth(:right, auth, h, value), update_stack(stack, auth_at_right(leaf), fullnodes, h)}
			_ ->
			  raise ArgumentError, message: "the argument value is invalid"
		      end
      update_both(auth, stack, fullnodes, leaf, h + 1)
    else
      {auth, stack}
    end
  end
  
  defp gen_merkle_path({current_auth, acc}, stack, fullnodes, size, leaf) when leaf < size do
    {new_auth, stack} = update_both(current_auth, stack, fullnodes, leaf, 0)
    gen_merkle_path({new_auth, acc ++ [new_auth]}, stack, fullnodes, size, leaf + 1)
  end

  defp gen_merkle_path({_auth, acc}, _stack, _fullnodes, size, leaf) when leaf == size do
    acc
  end

  defp auth0(nodes) do
    nodes
    |> Enum.filter_map(fn x -> is_list(x) end, &({:right, Enum.at(&1, 1)}))
  end

  defp stack0(nodes) do
    nodes
    |> Enum.filter_map(fn x -> is_list(x) end, &({:left, Enum.at(&1, 0)}))
  end

  @doc """
  Return a list that contains the authentication path to the MerkleRoot.

 
      iex(1)> ls = ["a", "b", "c", "d"]
      iex(2)> Hashtree.merkle_path(ls)
      [[right: "3e23e8160039594a33894f6564e1b1348bbd7a0088d42c4acb73eeaed59c009d",
      right: "d3a0f1c792ccf7f1708d5422696263e35755a86917ea76ef9242bd4a8cf4891a"],
      [left: "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb",
      right: "d3a0f1c792ccf7f1708d5422696263e35755a86917ea76ef9242bd4a8cf4891a"],
      [right: "18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4",
      left: "62af5c3cb8da3e4f25061e829ebeea5c7513c54949115b1acc225930a90154da"],
      [left: "2e7d2c03a9507ae265ecf5b5356885a53393a2029d241394997265a1a25aefc6",
      left: "62af5c3cb8da3e4f25061e829ebeea5c7513c54949115b1acc225930a90154da"]]
  """
  
  @spec merkle_path(list) :: list
  def merkle_path(data) do
    fullnodes = gen_fullnodes(data)
    gen_merkle_path({auth0(fullnodes), [auth0(fullnodes)]}, stack0(fullnodes), fullnodes, length(fullnodes), 0)
  end

  defp join({:left, x}, acc), do: sha256(x <> acc)

  defp join({:right, x}, acc), do: sha256(acc <> x)

  @doc """
  Authenticate target data.
  After successful authentication, {:ok, target data} is returned.
  If it fails, it returns {:error, target data}.
  
 
      iex(1)> ls = ["a", "b", "c", "d"]
      iex(2)> root = Hashtree.merkle_root(ls)
      iex(3)> path = Hashtree.merkle_path(ls)
      iex(4)> target = Enum.at(ls, 1)
      iex(5)> auth_path = Enum.at(path, 1)  
      iex(6)> Hashtree.verify(target, root, auth_path)
      {:ok, "b"}
  """
  @spec verify(String.t, String.t, list) :: {:ok, String.t} | {:error, String.t}
  def verify(target, root, path) do
    if root == path |>
      Enum.reduce(sha256(target), &join(&1, &2)) do
      {:ok, target}
    else
      {:error, target}
    end
  end
  
end
