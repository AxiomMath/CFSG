module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Sl25Strict
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog

@[expose] def d5Words : List (List ℕ) :=
  [[5, 6, 1, 2, 3, 7, 5, 6, 5, 7, 6, 7, 2, 1, 6, 4, 5, 7, 4],
   [1, 7, 5, 2, 3, 7, 4, 2, 5, 6, 3, 2, 1, 6, 5, 6, 1]]

@[expose] def sl25s (a b c d : ZMod 5) (h : a * d - b * c = 1) : SL25S :=
  ⟨⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩⟩

@[expose] def imgD5 : List SL25S :=
  [sl25s 1 3 1 4 (by decide),
    sl25s 2 2 1 4 (by decide)]

@[expose] def u0Word : List ℕ :=
  [2, 4, 3, 5, 4, 7, 2, 5, 7, 2, 7, 1, 3, 6, 7, 2, 7, 2, 3, 2, 1, 6, 5]

@[expose] def c0Word : List ℕ :=
  [7, 2, 1, 7, 3, 4, 1, 6, 5, 2, 1, 6, 3, 1, 5]

@[expose] def rpWord : List ℕ :=
  [5, 6, 7, 5, 4, 7, 2, 1, 3, 2, 6, 3, 5, 6, 3, 1, 2, 3, 7, 5, 6, 5, 7, 3, 6, 1]

@[expose] def ckWords : List (List ℕ) :=
  [[5, 2, 3, 7, 5, 6, 5, 7, 3, 7, 2, 7, 7, 1, 7, 5, 7, 2],
   [5, 3, 2, 7, 2, 3, 5, 4, 1, 3, 3, 7, 5, 6, 5, 7, 3, 6, 1, 2, 6],
   [6, 2, 3, 2, 6, 5, 3, 6, 2, 1, 3, 7, 1, 6, 5, 2],
   [1, 2, 3, 2, 7, 2, 7, 6, 2, 6, 4, 3, 7, 5, 1, 2, 6]]

end CFSG.EvenSporadicStandard.HNRecog
