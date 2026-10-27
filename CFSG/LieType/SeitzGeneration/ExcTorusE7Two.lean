module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7TwoWord : List (Fin Tag.E7.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
   4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]

@[expose] def e7TwoMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def e7TwoBasis : List (List ℤ) :=
  [[-1, 1, 1, 1, 1, 1, 2], [2, 1, 2, -1, 2, 0, 2], [-2, -1, -2, 1, -1, 1, 0],
   [0, -2, 1, -2, 0, -2, -1], [-2, 1, 0, 2, -1, 1, -1], [1, -2, -1, -1, -1, -2, -1],
   [1, 1, 2, 1, 1, 0, 2]]

@[expose] def e7TwoBasisInv : List (List ℤ) :=
  [[-1, -1, 0, 0, -1, -1, 1], [2, 10, 2, -1, 8, 7, -5], [0, 9, 3, 0, 7, 5, -3],
   [-2, -21, -6, 1, -16, -13, 9], [-3, -40, -12, 2, -31, -25, 16], [-1, 7, 3, 0, 5, 3, -2],
   [2, 17, 5, -1, 13, 11, -7]]

theorem e7Two_wordMat :
    wordMat Tag.E7 e7TwoWord = toMat Tag.E7.rank e7TwoMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Two_pow : (wordMat Tag.E7 e7TwoWord) ^ 2 = 1 := by
  rw [e7Two_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Two_charpoly :
    (wordMat Tag.E7 e7TwoWord).charpoly =
      ([2, 2, 2, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Two_wordMat]
  exact charpoly_of_basis e7TwoMat e7TwoBasis e7TwoBasisInv [2, 2, 2, 2, 2, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E7_two
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 7 := by
  have h := exists_elemAbelian_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
    (IsWeylMatrix.of_word Tag.E7 e7TwoWord) [2, 2, 2, 2, 2, 2, 2]
    e7Two_charpoly e7Two_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
