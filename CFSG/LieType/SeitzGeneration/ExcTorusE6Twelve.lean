module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6TwelveWord : List (Fin Tag.E6.rank) :=
  [0, 5, 4, 3, 1, 2]

@[expose] def e6TwelveMat : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0], [0, -1, 0, 1, 0, 0], [1, 0, -1, 1, 0, 0], [1, -1, -1, 1, 1, 0],
   [1, -1, -1, 1, 0, 1], [1, -1, -1, 1, 0, 0]]

@[expose] def e6TwelveBasis : List (List ℤ) :=
  [[0, -1, -2, 2, 0, -2], [0, 0, 1, 0, 0, 0], [1, -1, -1, 0, 2, -2], [0, 0, 1, 0, 0, -1],
   [1, 0, 1, -2, 1, 0], [1, -1, -1, -1, 2, -2]]

@[expose] def e6TwelveBasisInv : List (List ℤ) :=
  [[1, -1, 1, 0, 2, -2], [-1, -4, 2, 2, 0, -2], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, -1],
   [-1, 0, 1, 0, -1, 0], [0, 1, 0, -1, 0, 0]]

theorem e6Twelve_wordMat :
    wordMat Tag.E6 e6TwelveWord = toMat Tag.E6.rank e6TwelveMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Twelve_pow : (wordMat Tag.E6 e6TwelveWord) ^ 12 = 1 := by
  rw [e6Twelve_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Twelve_charpoly :
    (wordMat Tag.E6 e6TwelveWord).charpoly =
      ([3, 12].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Twelve_wordMat]
  exact charpoly_of_basis e6TwelveMat e6TwelveBasis e6TwelveBasisInv [3, 12]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_twelve
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    SylowTorus (adjointGroup Tag.E6 K) p 1 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6TwelveWord) [3, 12] e6Twelve_charpoly
    e6Twelve_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
