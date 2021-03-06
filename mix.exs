defmodule Hashtree.Mixfile do
  use Mix.Project

  @description """
  This module generates MerkleRoot and MerklePath. And it also verifies data given in the argument.
  SHA256 is used for the hashing.
  """

  def project do
    [app: :hashtree,
     version: "0.1.0",
     elixir: "~> 1.4",
     name: "Hashtree",
     description: @description,
     package: package(),
     build_embedded: Mix.env == :prod,
     start_permanent: Mix.env == :prod,
     deps: deps()]
  end

  defp package do
     [ maintainers: ["rodeeem"],
       licenses: ["MIT"], 
       links: %{ "Github" => "https://github.com/rodeeem/Hashtree" } ]
  end

  # Configuration for the OTP application
  #
  # Type "mix help compile.app" for more information
  def application do
    # Specify extra applications you'll use from Erlang/Elixir
    [extra_applications: [:logger]]
  end

  # Dependencies can be Hex packages:
  #
  #   {:my_dep, "~> 0.3.0"}
  #
  # Or git/path repositories:
  #
  #   {:my_dep, git: "https://github.com/elixir-lang/my_dep.git", tag: "0.1.0"}
  #
  # Type "mix help deps" for more examples and options
  defp deps do
    [
      {:ex_doc, "~> 0.11"}, 
      {:earmark, ">= 0.0.0"}
    ]
    end
      
end
