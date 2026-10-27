module

public import CFSG.Sporadic.SuzOddCore.CTICheckInputs
public import CFSG.LieType.Multipliers.L34Data

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.LieType.Multipliers.L34

@[expose] def suzDWordA : List Nat := [1, 1, 1, 1, 0, 0, 4, 4, 1, 3, 3, 3, 3, 1, 1, 0, 4]

@[expose] def suzDWordB : List Nat :=
  [1, 1, 1, 1, 0, 1, 1, 1, 1, 3, 3, 3, 3, 4, 0, 0, 4, 1, 1, 1, 1]

@[expose] def suzDGenWords : List (List (Fin 2 × Bool)) :=
  ["BBBABBABABABAbABBAbABABBBBAbbABAb", "ABAbABBAbABABBaBabbaBBabAb",
    "ABAbABBAbABABBaBabbaBBabAb", "ABBababbABBAbABAbbAABBAbbABAb",
    "abaBaBBAbABabaBBabba"].map parseWord

@[expose] def suzDLetterTab (aT aI bT bI : Tab) : Fin 2 × Bool → Tab
  | (0, true) => aT
  | (0, false) => aI
  | (1, true) => bT
  | (1, false) => bI

@[expose] def suzDWordTab (aT aI bT bI : Tab) (w : List (Fin 2 × Bool)) : Tab :=
  w.foldr (fun l acc => comp 42 (suzDLetterTab aT aI bT bI l) acc) (idTab 42)

@[expose] def suzDBridgeCheck : Bool :=
  let aT := wordTab 42 dGens suzDWordA
  let bT := wordTab 42 dGens suzDWordB
  let aI := invTab 42 aT
  let bI := invTab 42 bT
  aI.size == 42 && bI.size == 42 && comp 42 aI aT == idTab 42 && comp 42 bI bT == idTab 42 &&
    rels.all (fun r => suzDWordTab aT aI bT bI r == idTab 42) &&
    (List.range 5).all fun j => suzDWordTab aT aI bT bI (suzDGenWords.getD j []) == dGens[j]!

end CFSG.EvenSporadicStandard.Induction
