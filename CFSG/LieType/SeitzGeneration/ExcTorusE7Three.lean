module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7ThreeWord : List (Fin Tag.E7.rank) :=
  [0, 3, 1, 2, 0, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4]

@[expose] def e7ThreeMat : List (List ℤ) :=
  [[0, -1, -1, 1, 0, 0, 1], [1, -1, -1, 1, -1, 1, 1], [1, -1, -2, 2, -1, 0, 2],
   [1, -1, -2, 2, -2, 1, 3], [0, -1, -1, 2, -2, 1, 2], [0, -1, 0, 1, -1, 0, 2],
   [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7ThreeBasis : List (List ℤ) :=
  [[2, 2, 1, 1, 5, 1, -1], [3, -2, 3, -1, 9, 0, -1], [4, 0, 1, -2, 12, 1, -2],
   [6, -2, 2, 1, 16, 1, -4], [5, 1, -1, -2, 12, 1, -3], [4, 1, 1, 1, 6, 0, -2],
   [3, 1, 1, 1, 1, -1, -1]]

@[expose] def e7ThreeBasisInv : List (List ℤ) :=
  [[-3, 10, -13, -7, 6, 23, -17], [2, -4, 5, 3, -2, -11, 8], [-4, -7, 12, 1, -8, 3, 1],
   [4, 5, -9, 0, 6, -5, 1], [4, 1, -3, 2, 3, -11, 6], [-10, 5, -3, -9, -2, 39, -25],
   [7, 20, -31, -6, 19, 6, -11]]

theorem e7Three_wordMat :
    wordMat Tag.E7 e7ThreeWord = toMat Tag.E7.rank e7ThreeMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Three_pow : (wordMat Tag.E7 e7ThreeWord) ^ 3 = 1 := by
  rw [e7Three_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Three_charpoly :
    (wordMat Tag.E7 e7ThreeWord).charpoly =
      ([1, 3, 3, 3].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Three_wordMat]
  exact charpoly_of_basis e7ThreeMat e7ThreeBasis e7ThreeBasisInv [1, 3, 3, 3]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E7_three
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    ∃ E : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3]
    e7Three_charpoly e7Three_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
