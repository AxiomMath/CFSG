module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def decodeRt (str : String) : Array (Array ℕ) :=
  ((str.splitOn ";").map fun row =>
    ((row.splitOn ",").map fun t => t.toNat?.getD 0).toArray).toArray

@[expose] def decodePar (str : String) : Array (ℕ × ℕ) := (decodePairs str).toArray

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
