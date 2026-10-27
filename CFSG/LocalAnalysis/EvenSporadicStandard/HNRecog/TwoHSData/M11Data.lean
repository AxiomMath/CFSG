module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables

public section

namespace CFSG.EvenSporadicStandard.HNRecog

@[expose] def y0Word : List ℕ :=
  [1, 5, 7, 2, 7, 4, 2, 1, 6, 1, 3, 1, 2, 5, 3, 7, 2, 7, 1, 2, 1, 6, 1]

@[expose] def vWord : List ℕ :=
  [5, 6, 1, 2, 3, 2, 7, 2, 7, 6, 3, 5, 3, 2, 6, 5, 3, 6, 1, 2, 3, 1, 6, 4, 7, 6, 1, 3, 7]

@[expose] def i0Word : List ℕ := [7, 4, 7]

@[expose] def n1Word : List ℕ := [1, 2, 7, 6, 5, 4, 3, 5, 7, 2, 7, 3, 5, 6, 1, 2, 6, 1]

@[expose] def rho0Word : List ℕ := [7, 4, 7, 3, 4, 3]

@[expose] def ck2Word : List ℕ :=
  [1, 2, 7, 5, 7, 4, 1, 2, 6, 3, 7, 2, 7, 3, 6, 7, 2, 7, 2, 3, 6, 1, 2, 5]

@[expose] def ck3Word : List ℕ :=
  [6, 1, 5, 1, 2, 1, 6, 5, 3, 7, 5, 6, 5, 7, 3, 2, 7, 2, 7, 5, 3, 2, 4, 5, 7, 3, 7, 2]

@[expose] def ck4Word : List ℕ := [3, 7, 2, 7, 4, 2, 3, 2, 3, 1, 2, 1, 6, 1]

@[expose] def cBWord : List ℕ :=
  [2, 1, 7, 6, 3, 5, 4, 3, 6, 1, 6, 1, 5, 1, 3, 2, 1, 6, 3, 2, 3, 2, 3, 7, 5, 6, 5, 7, 3, 2, 5, 6,
    1]

@[expose] def m11Probes : List (List ℕ) :=
  [[1, 2], [1, 4], [1, 3], [1, 2, 2], [1, 2, 5], [1, 5, 2]]

end CFSG.EvenSporadicStandard.HNRecog
