module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7FourteenWord : List (Fin Tag.E7.rank) :=
  [0, 1, 3, 2, 6, 5, 4, 3, 2]

@[expose] def e7FourteenMat : List (List ℤ) :=
  [[0, 1, 0, -1, 1, 0, 0], [1, 1, 0, -1, 0, 1, 0], [1, 1, 0, -1, 1, 0, 0], [1, 2, 0, -1, 0, 1, 0],
   [1, 1, -1, 0, 0, 1, 0], [1, 1, -1, 0, 0, 0, 1], [1, 1, -1, 0, 0, 0, 0]]

@[expose] def e7FourteenBasis : List (List ℤ) :=
  [[2, -1, -1, 0, -1, -1, -1], [-1, -2, -2, -1, 0, -1, -1], [0, -2, -2, -1, -1, -2, -2],
   [0, -2, -4, -3, -1, -1, -2], [-1, -1, -2, -3, -2, -1, 0], [0, -1, -2, -2, -1, 0, 0],
   [-1, -1, -1, -1, 0, 0, 0]]

@[expose] def e7FourteenBasisInv : List (List ℤ) :=
  [[2, 0, -2, 1, 1, -3, 2], [-1, 1, 0, 0, 0, 1, -3], [2, -2, -1, 1, 1, -4, 5],
   [-3, 1, 3, -2, -2, 6, -5], [3, 1, -4, 2, 2, -6, 3], [-2, -2, 3, -1, -2, 4, 0],
   [1, 2, -2, 0, 1, -1, -1]]

theorem e7Fourteen_wordMat :
    wordMat Tag.E7 e7FourteenWord = toMat Tag.E7.rank e7FourteenMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Fourteen_pow : (wordMat Tag.E7 e7FourteenWord) ^ 14 = 1 := by
  rw [e7Fourteen_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Fourteen_charpoly :
    (wordMat Tag.E7 e7FourteenWord).charpoly =
      ([2, 14].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Fourteen_wordMat]
  exact charpoly_of_basis e7FourteenMat e7FourteenBasis e7FourteenBasisInv [2, 14]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_fourteen
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 14) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7FourteenWord) [2, 14] e7Fourteen_charpoly
    e7Fourteen_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
