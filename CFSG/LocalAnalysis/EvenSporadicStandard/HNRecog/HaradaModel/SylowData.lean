module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

@[expose] def sWords : List (List ℕ) :=
  [[7], [3, 2, 3], [2, 7, 5, 4, 6, 5, 7, 2, 7], [6, 1, 7, 2, 7, 2, 7, 1, 6],
    [2, 7, 1, 7, 3, 4, 3, 2, 6]]

@[expose] def comW (x y : List ℕ) : List ℕ := x ++ y ++ x.reverse ++ y.reverse

@[expose] def tpPairs : List (ℕ × ℕ) := [(0, 1), (0, 4), (1, 2), (2, 3), (2, 4), (3, 4)]

@[expose] def tpWords : List (List ℕ) :=
  tpPairs.map fun p => comW (sWords.getD p.1 []) (sWords.getD p.2 [])

@[expose] def w0Extra : List (List ℕ) :=
  [[1, 2, 7, 3, 7, 1, 6, 3, 1, 2, 3, 1, 2, 1, 6, 1],
    [7, 4, 5, 4, 7, 1, 3, 2, 3, 5, 6, 3, 5, 3, 6, 7, 2, 7, 2, 3, 6, 1, 2, 1, 6, 5]]

@[expose] def tGens : List (List ℕ) :=
  [[2, 7, 1, 7, 3, 4, 3, 2, 6], [2, 7, 5, 4, 6, 5, 7, 2, 7, 7], [6, 1, 7, 2, 7, 2, 7, 1, 6, 7]]

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
