module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7FourWord : List (Fin Tag.E7.rank) :=
  [1, 2, 3, 1, 4, 3]

@[expose] def e7FourMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, -1, 1, 0], [1, 0, 1, -1, 0, 1, 0], [0, 0, 2, -1, 0, 1, 0],
   [0, 1, 1, -1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7FourBasis : List (List ℤ) :=
  [[2, -4, 4, -1, -1, -1, -1], [1, 0, -1, -2, 1, -1, 0], [2, -2, 1, 1, 3, 0, 0],
   [2, 0, -2, -2, 5, -1, 1], [1, 2, -4, 1, 2, 0, 0], [0, 4, -6, 1, 1, 0, 0],
   [-2, 1, 1, 2, 2, -1, -1]]

@[expose] def e7FourBasisInv : List (List ℤ) :=
  [[7, -18, -34, 9, 59, -40, 2], [9, -24, -47, 12, 82, -56, 3], [6, -16, -31, 8, 54, -37, 2],
   [1, -2, 0, 1, -2, 2, 0], [-1, 2, 2, -1, -2, 1, 0], [-2, 3, -1, -2, 7, -6, 0],
   [3, -7, -5, 4, 3, -1, 0]]

theorem e7Four_wordMat : wordMat Tag.E7 e7FourWord = toMat Tag.E7.rank e7FourMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Four_pow : (wordMat Tag.E7 e7FourWord) ^ 4 = 1 := by
  rw [e7Four_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Four_charpoly :
    (wordMat Tag.E7 e7FourWord).charpoly = ([1, 1, 1, 4, 4].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Four_wordMat]
  exact charpoly_of_basis e7FourMat e7FourBasis e7FourBasisInv [1, 1, 1, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_four
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    SylowTorus (adjointGroup Tag.E7 K) p 2 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7FourWord) [1, 1, 1, 4, 4] e7Four_charpoly
    e7Four_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
