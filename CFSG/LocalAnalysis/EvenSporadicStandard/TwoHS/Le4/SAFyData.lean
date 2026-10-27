module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Data

public section

namespace CFSG.EvenSporadicStandard.TwoHS

@[expose] def fyRWord : List ℕ :=
  [1, 2, 4, 5, 3, 2, 3, 4, 1, 3, 2, 3, 6, 3, 4, 5, 1, 2, 3, 2, 6, 1, 5]

@[expose] def fyCWords : List (List ℕ) :=
  [[1, 2, 1, 4, 3, 2, 3, 4, 6, 3, 5, 4, 2, 3, 6],
   [1, 3, 2, 1, 4, 3, 2, 3, 4, 6, 3, 5, 4, 2, 3, 6, 3],
   [5, 3, 2, 1, 6, 3, 2, 1, 4, 6, 3, 5, 6, 1, 2, 3, 4, 1, 3, 2, 3, 5, 4, 3, 2],
   [1, 2, 1, 3, 4, 3, 2, 3, 2, 5, 4, 3, 6, 3, 5, 2, 3, 4, 3, 6, 3, 4]]

@[expose] def fyAWord : List ℕ :=
  [4, 5, 2, 3, 6, 5, 3, 2, 4, 3, 6, 5, 2, 3, 1, 2, 3, 4, 1, 2, 3, 2, 3]

@[expose] def fyLWord : List ℕ :=
  [5, 2, 4, 3, 2, 5, 3, 2, 1, 4, 6, 1, 3, 4, 5, 6, 3, 2, 3, 6, 5, 4]

end CFSG.EvenSporadicStandard.TwoHS
