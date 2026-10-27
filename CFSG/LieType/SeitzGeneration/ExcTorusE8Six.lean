module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8SixWord : List (Fin Tag.E8.rank) :=
  [1, 4, 3, 1, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2,
   4, 3, 1, 5, 4, 3, 2, 0]

@[expose] def e8SixMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1, 0, 0], [-2, 1, 0, -1, 1, 1, 0, 0], [-3, 0, 0, 0, 1, 1, 0, 0],
   [-4, 1, -1, 0, 1, 2, 0, 0], [-3, 0, -1, 0, 1, 2, 0, 0], [-3, 0, 0, 0, 0, 2, 0, 0],
   [-2, 0, 0, 0, 0, 1, 1, -1], [-1, 0, 0, 0, 0, 0, 1, 0]]

@[expose] def e8SixBasis : List (List ℤ) :=
  [[-1, 2, 1, 0, -2, 0, 1, -1], [2, 3, -1, -5, 1, 6, -1, -5], [-2, 2, -2, -4, 0, 6, -1, -4],
   [0, 8, 1, -3, -1, 7, 1, -5], [-2, 5, -2, -1, 2, 4, -1, -3], [1, 5, 1, -1, -2, 2, 0, -3],
   [1, 3, 1, -2, 0, 4, 1, -2], [1, 2, 2, 0, -2, 2, 1, 0]]

@[expose] def e8SixBasisInv : List (List ℤ) :=
  [[-20, -14, 7, 12, -12, 10, 4, -15], [8, 2, 0, -14, 7, 3, 11, 4],
   [44, 34, -18, -20, 25, -27, -18, 35], [-29, -14, 5, 34, -21, 2, -17, -18],
   [14, 11, -6, -6, 8, -9, -6, 11], [-10, -5, 2, 11, -7, 1, -5, -6],
   [-36, -26, 13, 22, -22, 18, 8, -28], [15, 4, 0, -26, 13, 5, 20, 8]]

theorem e8Six_wordMat :
    wordMat Tag.E8 e8SixWord = toMat Tag.E8.rank e8SixMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Six_pow : (wordMat Tag.E8 e8SixWord) ^ 6 = 1 := by
  rw [e8Six_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Six_charpoly :
    (wordMat Tag.E8 e8SixWord).charpoly =
      ([6, 6, 6, 6].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Six_wordMat]
  exact charpoly_of_basis e8SixMat e8SixBasis e8SixBasisInv [6, 6, 6, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E8_six
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    ∃ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6]
    e8Six_charpoly e8Six_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
