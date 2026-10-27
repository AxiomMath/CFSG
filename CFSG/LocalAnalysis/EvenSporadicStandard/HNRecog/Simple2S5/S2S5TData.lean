module

public import Init

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] def tLetters : List (List (List Nat)) :=
  [[[2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1], [2, 2, 1, 2, 2, 2, 1]], [[2, 2, 2, 1, 2, 2, 2, 1, 2, 1,
   2, 1, 2, 1], [1, 2, 1, 2]]]

@[expose] def mLetters : List (List (List Nat)) :=
  [[[2, 2, 2, 2, 1, 2, 1, 2, 2], [2, 2, 1, 2, 2, 2, 1]], [[2, 1, 2, 2, 1, 2, 2], [1, 2, 1, 2]]]

@[expose] def uLetters : List (List Nat) :=
  [[1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2], [2, 1, 2, 2, 2, 2]]

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
