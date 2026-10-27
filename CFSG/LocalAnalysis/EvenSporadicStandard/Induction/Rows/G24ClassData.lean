module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2.Native

@[expose] def clsNums : Array Nat := parseNums (include_str "G24ClassTbl.txt")

@[expose] def rdGens : Array (Array Nat) :=
  (List.range 8).toArray.map fun i => clsNums.extract (8192 + 1365 * i) (8192 + 1365 * (i + 1))

@[expose] def rdPar : Array Nat := clsNums.extract 19112 23207

@[expose] def rdPg : Array Nat := clsNums.extract 23207 27302

@[expose] def rdList : Array (Array Nat) := buildList (idA nn) rdPar (rmulOp rdGens rdPg)

end CFSG.EvenSporadicStandard.G24Aut
