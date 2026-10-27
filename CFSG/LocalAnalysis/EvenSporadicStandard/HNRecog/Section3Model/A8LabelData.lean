module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

@[expose] def a8SX : List (ℕ × ℕ) := [(1, 1), (2, 1), (1, 3)]

@[expose] def a8SY : List (ℕ × ℕ) := [(1, 7), (2, 4), (1, 13)]

@[expose] def a8SU : List (ℕ × ℕ) := [(1, 1), (2, 1), (1, 10), (2, 4), (1, 10), (2, 9), (1, 7)]

@[expose] def a8Row : OrbRow where
  conj := []
  m := 105
  n := 768
  stab := [[(1, 4), (2, 2)], [(1, 7)], [(2, 7)], [(1, 3), (2, 4)], [(1, 1), (2, 3), (1, 2), (2, 13)]]

@[expose] def a8WZ : List ℕ :=
  [6, 5, 6, 1, 2, 1, 6, 5, 3, 7, 5, 6, 5, 7, 3, 1, 7, 2, 7, 3, 5, 2, 1, 1, 6, 7, 1, 7, 6, 4, 1]

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
