module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def tab4Row0 : OrbRow where
  conj := [3, 5, 3, 5, 7, 5, 2, 7, 4, 7]
  m := 105
  n := 768
  stab := [[(2, 13), (1, 10), (2, 5), (2, 6), (1, 5), (2, 1), (2, 2), (2, 8)],
           [(1, 11), (1, 11), (1, 3), (1, 7), (2, 13), (1, 6)],
           [(2, 9), (2, 3), (2, 4), (1, 1), (2, 5), (2, 1), (1, 1), (2, 2)]]

@[expose] def tab4Row1 : OrbRow where
  conj := [4, 2, 5, 4]
  m := 105
  n := 768
  stab := [[(1, 7), (1, 4), (2, 4), (1, 10), (1, 6), (1, 6), (1, 8)],
           [(2, 3), (1, 3), (2, 13), (1, 9), (1, 9)],
           [(1, 13), (2, 11), (1, 10), (1, 11), (1, 11), (2, 1), (2, 11)]]

@[expose] def tab4Row2 : OrbRow where
  conj := [6, 3, 1, 5, 2, 1]
  m := 56
  n := 1440
  stab := [[(2, 5), (1, 12), (1, 9), (1, 10), (2, 4), (2, 9), (1, 12)],
           [(1, 7), (2, 1), (1, 2), (1, 5), (1, 5), (2, 9)]]

@[expose] def tab4Row3 : OrbRow where
  conj := [7, 2, 3, 5]
  m := 1260
  n := 64
  stab := [[(1, 2), (2, 7), (2, 7), (1, 5)],
           [(1, 2), (1, 6), (2, 1), (1, 8), (1, 6), (1, 12), (2, 3), (2, 5)],
           [(1, 1), (2, 6), (1, 4), (1, 11), (1, 10), (2, 3), (1, 10), (2, 12)],
           [(2, 9), (1, 10), (2, 4), (1, 9), (2, 1), (1, 13), (2, 9)],
           [(1, 12), (2, 11), (2, 13), (1, 9), (2, 3), (1, 8)]]

@[expose] def tab4Row4 : OrbRow where
  conj := [6, 4, 2, 4]
  m := 336
  n := 240
  stab := [[(1, 6), (2, 3), (2, 11), (1, 10), (1, 6), (1, 13)],
           [(1, 5), (2, 1), (1, 6), (2, 10), (1, 1), (2, 11), (2, 3), (2, 5)],
           [(1, 8), (2, 13), (1, 13), (1, 13)]]

@[expose] def tab4Row5 : OrbRow where
  conj := [2, 7, 3, 5, 2]
  m := 336
  n := 240
  stab := [[(2, 5), (1, 9), (2, 9), (1, 2)],
           [(1, 12), (1, 5), (2, 8), (1, 13), (2, 10), (2, 9), (1, 5)]]

@[expose] def tab4W0 : List ℕ :=
  [1, 6, 5, 1, 3, 7, 5, 6, 5, 7, 3, 3, 2, 3, 1, 2, 3, 7, 6, 7]

@[expose] def tab4W1 : List ℕ :=
  [5, 7, 1, 7, 4, 3, 6, 1, 7, 2, 7, 3, 1, 3, 6, 7, 2, 7, 2, 3, 5, 6, 1, 2, 6, 5, 6, 1]

@[expose] def tab4W3 : List ℕ :=
  [1, 2, 1, 6, 3, 7, 5, 6, 5, 7, 5, 3, 7, 4, 5, 7, 3]

@[expose] def tab4Wab : List ℕ :=
  [1, 7, 4, 7, 1, 2, 1, 6, 3, 5, 6, 2, 3, 1, 2, 1, 6, 5, 1]

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
