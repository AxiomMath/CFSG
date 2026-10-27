module

public section

namespace CFSG.QuasithinUnique.A5.B7

@[expose] def b7Decode (s : String) : List Int :=
  s.toList.filterMap fun ch =>
    if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
    else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
    else none

@[expose] def b7ExplicitWords : List (List Int) := [
  b7Decode (
      "bABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAba" ++
      "abAABAbaabAABAbaabAABAbaabAABAbaabACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
      "AbaabAABAbaabAAAbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABcaAB" ++
      "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACacABAbaabAABAbaabAABAbaa" ++
      "bAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAA" ++
      "BAbaabAABAbaabAAABAcACaacBCbabABAbbCCbaBBBBAba"),
  b7Decode (
      "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbaABAbaabAABAbaabAABAbaa" ++
      "bAABAbaabAABAbaabAABAbaabAABAbaabAABcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
      "AbaabAABAbaabAACacABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACACCCC" ++
      "CBaBABCBBBBaBBababAcaBab"),
  b7Decode (
      "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAcABAbaabAABAbaabAABAbaab" ++
      "AABAbaabAABAbaabAABAbaabAABAbaabACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAb" ++
      "aabAABAbaabAAAcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACbbABAb" ++
      "aabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBbacbACbAbABAAcbcAAcccbCCac" ++
      "Bc"),
  b7Decode (
      "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaab" ++
      "AABAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
      "abAABAbaabACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAbaABAbaa" ++
      "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABcaABAbaabAABAbaabAABAbaabAAB" ++
      "AbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaa" ++
      "bAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBbaaABAba" ++
      "abAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABCBBaBaBBBAcbCBcaBAcBaCBCaB" ++
      "aB")
]

end CFSG.QuasithinUnique.A5.B7
