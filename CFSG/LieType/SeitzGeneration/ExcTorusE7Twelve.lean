module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7TwelveWord : List (Fin Tag.E7.rank) :=
  [0, 1, 5, 4, 3, 2]

@[expose] def e7TwelveMat : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0, 0], [1, 0, -1, 0, 1, 0, 0], [1, 0, -1, 1, 0, 0, 0], [1, 1, -1, 0, 1, 0, 0],
   [1, 1, -1, 0, 0, 1, 0], [1, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7TwelveBasis : List (List ℤ) :=
  [[-2, 1, 0, -2, 0, 2, -2], [-3, 1, 1, -1, 1, -1, 1], [-4, 2, 1, -1, -2, 2, 0],
   [-6, 2, 2, -1, 0, 0, 0], [-5, 2, 2, 2, -3, 1, 2], [-4, 2, 1, -1, -2, 3, -1],
   [-3, 1, 1, 0, 0, 0, 0]]

@[expose] def e7TwelveBasisInv : List (List ℤ) :=
  [[-3, 0, 1, -1, -2, 2, 3], [-5, 0, 4, -4, -4, 2, 10], [-4, 0, -1, 1, -2, 4, 0],
   [0, 0, 0, -1, 0, 0, 2], [0, 1, -1, -1, 0, 1, 1], [1, 1, -2, 0, 1, 1, -2],
   [1, 1, -1, 0, 1, 0, -2]]

theorem e7Twelve_wordMat : wordMat Tag.E7 e7TwelveWord = toMat Tag.E7.rank e7TwelveMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Twelve_pow : (wordMat Tag.E7 e7TwelveWord) ^ 12 = 1 := by
  rw [e7Twelve_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Twelve_charpoly :
    (wordMat Tag.E7 e7TwelveWord).charpoly = ([1, 3, 12].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Twelve_wordMat]
  exact charpoly_of_basis e7TwelveMat e7TwelveBasis e7TwelveBasisInv [1, 3, 12]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_twelve
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7TwelveWord) [1, 3, 12] e7Twelve_charpoly
    e7Twelve_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
