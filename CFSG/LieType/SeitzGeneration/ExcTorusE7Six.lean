module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7SixWord : List (Fin Tag.E7.rank) :=
  [0, 2, 0, 3, 2, 5, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4]

@[expose] def e7SixMat : List (List ℤ) :=
  [[1, -1, 0, 0, 0, 0, 1], [1, -1, 0, 1, -1, 0, 1], [1, -1, 1, 0, -1, 0, 2],
   [1, -2, 1, 1, -2, 1, 2], [0, -2, 1, 1, -1, 0, 2], [0, -2, 1, 1, -1, 0, 1],
   [0, -1, 0, 1, -1, 0, 1]]

@[expose] def e7SixBasis : List (List ℤ) :=
  [[0, 1, -1, 0, -2, 0, -3], [-1, 0, 0, 0, -2, 0, 0], [0, 1, 0, 0, -5, 0, -3],
   [0, -1, 2, 1, -3, 0, 2], [-1, -2, -2, 1, -4, -3, -3], [-2, 1, 0, 2, -2, 2, 0],
   [-1, -2, -1, -2, -2, -3, 0]]

@[expose] def e7SixBasisInv : List (List ℤ) :=
  [[14, -1, -8, 6, -2, 0, 2], [4, 24, -6, 0, 2, -9, -8], [-22, 0, 13, -9, 3, 0, -3],
   [1, 8, -2, 0, 1, -3, -3], [-7, 0, 4, -3, 1, 0, -1], [4, -21, 1, 3, -3, 8, 8],
   [13, 8, -9, 5, -1, -3, -1]]

theorem e7Six_wordMat :
    wordMat Tag.E7 e7SixWord = toMat Tag.E7.rank e7SixMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Six_pow : (wordMat Tag.E7 e7SixWord) ^ 6 = 1 := by
  rw [e7Six_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Six_charpoly :
    (wordMat Tag.E7 e7SixWord).charpoly =
      ([2, 6, 6, 6].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Six_wordMat]
  exact charpoly_of_basis e7SixMat e7SixBasis e7SixBasisInv [2, 6, 6, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E7_six
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    ∃ E : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6]
    e7Six_charpoly e7Six_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
