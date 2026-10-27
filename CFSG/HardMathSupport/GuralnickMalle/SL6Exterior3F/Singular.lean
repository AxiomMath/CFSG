module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Matrix

noncomputable def isUnitDetEquivGL (K : Type) [Field K] :
    {M : Matrix (Fin 3) (Fin 3) K // IsUnit M.det} ≃ GL (Fin 3) K where
  toFun M := Matrix.GeneralLinearGroup.mk'' M.1 M.2
  invFun g := ⟨(g : Matrix (Fin 3) (Fin 3) K), Matrix.isUnits_det_units g⟩
  left_inv M := Subtype.ext (by simp)
  right_inv g := Units.ext (by simp)

theorem card_matrix_three (K : Type) [Field K] [Finite K] :
    Nat.card (Matrix (Fin 3) (Fin 3) K) = Nat.card K ^ 9 := by
  rw [Matrix.card_matrix, Nat.card_fin]

theorem card_GL_three (K : Type) [Field K] [Finite K] :
    Nat.card (GL (Fin 3) K) =
      (Nat.card K ^ 3 - 1) * (Nat.card K ^ 3 - Nat.card K) *
        (Nat.card K ^ 3 - Nat.card K ^ 2) := by
  let : Fintype K := Fintype.ofFinite K
  have h := Matrix.card_GL_field (𝔽 := K) (n := 3)
  rw [Fin.prod_univ_three] at h
  rw [← Nat.card_eq_fintype_card] at h
  simpa using h

theorem card_singular_eq (K : Type) [Field K] [Finite K] :
    Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} =
      Nat.card K ^ 9 - Nat.card (GL (Fin 3) K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  congr 1
  · rw [← Nat.card_eq_fintype_card, card_matrix_three]
  · rw [Fintype.card_congr (isUnitDetEquivGL K), ← Nat.card_eq_fintype_card]

theorem card_singular_eq_int (K : Type) [Field K] [Finite K] :
    (Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} : ℤ) =
      (Nat.card K : ℤ) ^ 8 + (Nat.card K : ℤ) ^ 7 - (Nat.card K : ℤ) ^ 5 -
        (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 := by
  classical
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hS := card_singular_eq K
  have hGL := card_GL_three K
  have hPle : Nat.card (GL (Fin 3) K) ≤ Nat.card K ^ 9 := by
    rw [hGL]
    calc (Nat.card K ^ 3 - 1) * (Nat.card K ^ 3 - Nat.card K) *
          (Nat.card K ^ 3 - Nat.card K ^ 2)
        ≤ Nat.card K ^ 3 * Nat.card K ^ 3 * Nat.card K ^ 3 := by
          refine Nat.mul_le_mul ?_ (Nat.sub_le _ _)
          exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = Nat.card K ^ 9 := by ring
  have hsum : Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} +
      Nat.card (GL (Fin 3) K) = Nat.card K ^ 9 := by
    rw [hS, Nat.sub_add_cancel hPle]
  have hsumZ : (Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} : ℤ) +
      (Nat.card (GL (Fin 3) K) : ℤ) = (Nat.card K : ℤ) ^ 9 := by
    exact_mod_cast hsum
  have h1 : 1 ≤ Nat.card K ^ 3 := by
    have h := pow_pos hqpos 3
    omega
  have h2 : Nat.card K ≤ Nat.card K ^ 3 := by
    have hp2 : 1 ≤ Nat.card K ^ 2 := by
      have h := pow_pos hqpos 2
      omega
    calc Nat.card K = Nat.card K * 1 := (mul_one _).symm
      _ ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hp2
      _ = Nat.card K ^ 3 := by ring
  have h3 : Nat.card K ^ 2 ≤ Nat.card K ^ 3 := by
    calc Nat.card K ^ 2 = Nat.card K ^ 2 * 1 := (mul_one _).symm
      _ ≤ Nat.card K ^ 2 * Nat.card K := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.card K ^ 3 := by ring
  have hGLZ : (Nat.card (GL (Fin 3) K) : ℤ) =
      ((Nat.card K : ℤ) ^ 3 - 1) * ((Nat.card K : ℤ) ^ 3 - Nat.card K) *
        ((Nat.card K : ℤ) ^ 3 - (Nat.card K : ℤ) ^ 2) := by
    rw [hGL, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    push_cast
    ring
  have hmain : (Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} : ℤ) =
      (Nat.card K : ℤ) ^ 9 - ((Nat.card K : ℤ) ^ 3 - 1) *
        ((Nat.card K : ℤ) ^ 3 - Nat.card K) *
        ((Nat.card K : ℤ) ^ 3 - (Nat.card K : ℤ) ^ 2) := by
    linarith
  calc (Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} : ℤ)
      = (Nat.card K : ℤ) ^ 9 - ((Nat.card K : ℤ) ^ 3 - 1) *
          ((Nat.card K : ℤ) ^ 3 - Nat.card K) *
          ((Nat.card K : ℤ) ^ 3 - (Nat.card K : ℤ) ^ 2) := hmain
    _ = (Nat.card K : ℤ) ^ 8 + (Nat.card K : ℤ) ^ 7 - (Nat.card K : ℤ) ^ 5 -
          (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 := by ring

theorem card_singular_le_pow (K : Type) [Field K] [Finite K] :
    Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} ≤
      Nat.card K ^ 8 + Nat.card K ^ 7 := by
  classical
  have hq2 : 2 ≤ Nat.card K := by
    have h := (Finite.one_lt_card : 1 < Nat.card K)
    omega
  have hmain := card_singular_eq_int K
  have hZ : (Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} : ℤ) ≤
      (Nat.card K : ℤ) ^ 8 + (Nat.card K : ℤ) ^ 7 := by
    rw [hmain]
    have hq2' : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq2
    have h1 : (0 : ℤ) ≤ (Nat.card K : ℤ) ^ 3 := by positivity
    have h2 : (0 : ℤ) ≤ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) - 1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  exact_mod_cast hZ

theorem card_singular_matrices_le (K : Type) [Field K] [Finite K] :
    Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} ≤
      (Nat.card K ^ 2 + Nat.card K + 1) * Nat.card K ^ 6 := by
  refine le_trans (card_singular_le_pow K) ?_
  have h : (Nat.card K ^ 2 + Nat.card K + 1) * Nat.card K ^ 6 =
      Nat.card K ^ 8 + Nat.card K ^ 7 + Nat.card K ^ 6 := by ring
  rw [h]
  omega

theorem card_singular_matrices_lt (K : Type) [Field K] [Finite K]
    (hq : 2 ≤ Nat.card K) :
    Nat.card {M : Matrix (Fin 3) (Fin 3) K // ¬ IsUnit M.det} < 2 * Nat.card K ^ 8 := by
  have h1 : Nat.card K ^ 7 < Nat.card K ^ 8 := by
    have hq1 : 1 < Nat.card K := by omega
    have hp : 0 < Nat.card K ^ 7 := pow_pos (by omega : 0 < Nat.card K) 7
    calc Nat.card K ^ 7 = Nat.card K ^ 7 * 1 := (mul_one _).symm
      _ < Nat.card K ^ 7 * Nat.card K := mul_lt_mul_of_pos_left hq1 hp
      _ = Nat.card K ^ 8 := by ring
  have h2 := card_singular_le_pow K
  omega

end CFSG.HardMathSupport.GuralnickMalle
