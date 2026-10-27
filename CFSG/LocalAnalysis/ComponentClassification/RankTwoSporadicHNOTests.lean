
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
public import CFSG.Sporadic.HNOddCore.SixCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

@[expose] def psO : List ℕ := [0, 1]

@[expose] def hnAOCheck (prog : List (ℕ × ℕ)) (pregs : List ℕ) (pool : Array (ℕ × ℕ))
    (wits : Array AWit) : Bool :=
  aCheck 1100 CFSG.Sporadic.HNOddCore.Native.om0Gens prog pregs pool psO 1024 wits

@[expose] def pairsOf : List ℕ → List (ℕ × ℕ)
  | a :: b :: r => (a, b) :: pairsOf r
  | _ => []

@[expose] def witsOf : ℕ → List ℕ → List AWit
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, 0 :: r => .skip :: witsOf f r
  | f + 1, (_ + 1) :: l :: r => .ord4 (r.take l) (r.getD l 0) :: witsOf f (r.drop (l + 1))
  | _ + 1, [_ + 1] => []

@[expose] def decodePairsO (s : String) : List (ℕ × ℕ) := pairsOf (parseNatsHN s).toList

@[expose] def decodeAO (s : String) : Array AWit :=
  (witsOf (parseNatsHN s).size (parseNatsHN s).toList).toArray

end CFSG.ComponentClassification.RankTwoSporadic.HN
