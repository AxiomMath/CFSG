module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8ThreeWord : List (Fin Tag.E8.rank) :=
  [1, 3, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2,
   0, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6,
   5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0]

@[expose] def e8ThreeMat : List (List ℤ) :=
  [[-2, 0, 0, 0, 0, 1, 0, 0], [-2, 0, 0, -1, 1, 1, 0, 0], [-3, 0, -1, 0, 1, 1, 0, 0],
   [-4, 1, -1, -1, 1, 2, 0, 0], [-3, 0, -1, 0, 0, 2, 0, 0], [-3, 0, 0, 0, 0, 1, 0, 0],
   [-2, 0, 0, 0, 0, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 1, -1]]

@[expose] def e8ThreeBasis : List (List ℤ) :=
  [[-1, 3, 1, -1, -2, 2, 1, -2], [2, 1, -1, -4, 1, 5, -1, -4], [-2, 4, -2, -2, 0, 6, -1, -3],
   [0, 8, 1, -4, -1, 8, 1, -6], [-2, 7, -2, 1, 2, 2, -1, -2], [1, 4, 1, -2, -2, 4, 0, -3],
   [1, 2, 1, -3, 0, 4, 1, -3], [1, 1, 2, -2, -2, 4, 1, -1]]

@[expose] def e8ThreeBasisInv : List (List ℤ) :=
  [[-12, -12, 7, -2, -5, 13, 15, -11], [8, 2, 0, -14, 7, 3, 11, 4],
   [15, 20, -13, 14, 4, -25, -35, 17], [-29, -14, 5, 34, -21, 2, -17, -18],
   [4, 6, -4, 5, 1, -8, -11, 5], [-10, -5, 2, 11, -7, 1, -5, -6],
   [-21, -22, 13, -4, -9, 23, 28, -20], [15, 4, 0, -26, 13, 5, 20, 8]]

theorem e8Three_wordMat :
    wordMat Tag.E8 e8ThreeWord = toMat Tag.E8.rank e8ThreeMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Three_pow : (wordMat Tag.E8 e8ThreeWord) ^ 3 = 1 := by
  rw [e8Three_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Three_charpoly :
    (wordMat Tag.E8 e8ThreeWord).charpoly =
      ([3, 3, 3, 3].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Three_wordMat]
  exact charpoly_of_basis e8ThreeMat e8ThreeBasis e8ThreeBasisInv [3, 3, 3, 3]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E8_three
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    ∃ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3]
    e8Three_charpoly e8Three_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
