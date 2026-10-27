module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

@[expose] def uWords : List (List ℕ) :=
  [[7, 3, 2, 3, 7, 3, 2, 3], [7, 2, 5, 6, 1, 5, 2, 7, 1, 2, 1, 6, 5, 6],
    [5, 7, 4, 3, 7, 5, 6, 3, 2, 5, 6, 3, 5, 3, 6, 7, 2, 7, 2, 3, 6, 1, 2, 5, 6, 1],
    [7, 3, 6, 7, 2, 7, 2, 7, 6, 3], [4, 7, 4, 3, 7, 6, 2, 6, 7, 2, 7, 2, 3], [7]]

@[expose] def nExtraW : List ℕ :=
  [6, 1, 2, 1, 6, 5, 3, 2, 7, 2, 7, 6, 3, 5, 1, 7, 5, 6, 5, 7, 1, 4, 7, 4, 7, 1, 7]

@[expose] def normGens : List (List ℕ) := classz₁.centGens ++ [nExtraW]

@[expose] def typeBase : List ℕ := [1, 3, 45, 32]

@[expose] def bitOf (k i : ℕ) : ℕ := (k >>> i) % 2

@[expose] def lamC (k : ℕ) : ℕ := bitOf k 5

@[expose] def qmC (k : ℕ) : ℕ :=
  (bitOf k 0 * bitOf k 1 + bitOf k 2 * bitOf k 3 + bitOf k 4 + bitOf k 4 * bitOf k 5 +
    bitOf k 5) % 2

@[expose] def typeIdx (k : ℕ) : ℕ := 2 * lamC k + qmC k

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
