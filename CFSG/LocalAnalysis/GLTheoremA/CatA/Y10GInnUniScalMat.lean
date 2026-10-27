module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Data.Matrix.PEquiv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open Matrix

variable {K : Type} [Field K] {d : ℕ}

theorem uScal_mem_of_unitary (Q : ℕ) (A : GL (Fin d) K)
    (hdet : (A : Matrix (Fin d) (Fin d) K).det = 1)
    (hu : ((A : Matrix (Fin d) (Fin d) K).map (· ^ Q))ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1) :
    A ∈ StatedSU d Q K :=
  Subgroup.subset_closure ⟨hdet, hu⟩

@[expose] def uScal_torusMat (u : Kˣ) (a b : Fin d) : Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal fun k => if k = a then (u : K) else if k = b then ((u⁻¹ : Kˣ) : K) else 1

theorem uScal_det_torusMat (u : Kˣ) {a b : Fin d} (hab : a ≠ b) :
    (uScal_torusMat u a b).det = 1 := by
  have h0 : ∀ c : Fin d, c ≠ a ∧ c ≠ b →
      (fun k : Fin d => if k = a then (u : K) else if k = b then ((u⁻¹ : Kˣ) : K) else 1) c = 1 :=
    fun c hc => by simp [hc.1, hc.2]
  rw [uScal_torusMat, Matrix.det_diagonal, Fintype.prod_eq_mul a b hab h0]
  simp [Units.mul_inv, Ne.symm hab]

@[expose] noncomputable def uScal_torusGL (u : Kˣ) {a b : Fin d} (hab : a ≠ b) : GL (Fin d) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uScal_torusMat u a b)
    (by rw [uScal_det_torusMat u hab]; exact one_ne_zero)

theorem uScal_torusGL_val (u : Kˣ) {a b : Fin d} (hab : a ≠ b) :
    (uScal_torusGL u hab : Matrix (Fin d) (Fin d) K) = uScal_torusMat u a b :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem uScal_torusGL_mem {Q : ℕ} (hQ : Q ≠ 0) (u : Kˣ) (hu : u ^ (Q + 1) = 1) {a b : Fin d}
    (hab : a ≠ b) : uScal_torusGL u hab ∈ StatedSU d Q K := by
  refine uScal_mem_of_unitary Q _ ?_ ?_
  · rw [uScal_torusGL_val, uScal_det_torusMat u hab]
  · rw [uScal_torusGL_val, uScal_torusMat,
      Matrix.diagonal_map (f := fun x : K => x ^ Q) (zero_pow hQ),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    split_ifs with h1 h2
    · subst h1
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
    · subst h2
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, inv_pow, hu, inv_one, Units.val_one]
    · simp

@[expose] def uScal_rotMat (a b : Fin d) : Matrix (Fin d) (Fin d) K :=
  Matrix.diagonal (fun k => if k = a then (-1 : K) else 1) * Matrix.swap K a b

theorem uScal_swap_entry (a b x y : Fin d) :
    Matrix.swap K a b x y = 0 ∨ Matrix.swap K a b x y = 1 := by
  simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem uScal_swap_self (a b : Fin d) : Matrix.swap K a b a b = 1 := by
  have h := Matrix.swap_mul_apply_left (R := K) a b b (1 : Matrix (Fin d) (Fin d) K)
  rw [mul_one, Matrix.one_apply_eq] at h
  exact h

theorem uScal_det_rotMat {a b : Fin d} (hab : a ≠ b) : (uScal_rotMat (K := K) a b).det = 1 := by
  have hD : (Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1)).det = -1 := by
    rw [Matrix.det_diagonal, Fintype.prod_eq_single a (fun x hx => if_neg hx), if_pos rfl]
  have hS : (Matrix.swap K a b).det = -1 := by
    rw [Matrix.swap, Matrix.det_permutation, Equiv.Perm.sign_swap hab]
    simp
  rw [uScal_rotMat, Matrix.det_mul, hD, hS]
  norm_num

theorem uScal_rotMat_entry (a b x y : Fin d) :
    uScal_rotMat (K := K) a b x y = 0 ∨ uScal_rotMat (K := K) a b x y = 1 ∨
      uScal_rotMat (K := K) a b x y = -1 := by
  rw [uScal_rotMat, Matrix.diagonal_mul]
  rcases uScal_swap_entry (K := K) a b x y with h | h <;> split_ifs <;> simp [h]

theorem uScal_rotMat_swap_entry (a b : Fin d) : uScal_rotMat (K := K) a b a b = -1 := by
  rw [uScal_rotMat, Matrix.diagonal_mul, if_pos rfl, uScal_swap_self, mul_one]

theorem uScal_neg_one_pow {Q : ℕ} (τ : K ≃+* K) (hτQ : ∀ x, τ x = x ^ Q) : (-1 : K) ^ Q = -1 := by
  rw [← hτQ (-1), map_neg, map_one]

theorem uScal_pow_fix {Q : ℕ} (hQ : Q ≠ 0) (τ : K ≃+* K) (hτQ : ∀ x, τ x = x ^ Q) (z : K)
    (hz : z = 0 ∨ z = 1 ∨ z = -1) : z ^ Q = z := by
  rcases hz with rfl | rfl | rfl
  · exact zero_pow hQ
  · exact one_pow Q
  · exact uScal_neg_one_pow τ hτQ

theorem uScal_rotMat_map {Q : ℕ} (hQ : Q ≠ 0) (τ : K ≃+* K) (hτQ : ∀ x, τ x = x ^ Q) (a b : Fin d) :
    (uScal_rotMat (K := K) a b).map (· ^ Q) = uScal_rotMat a b := by
  ext x y
  simp only [Matrix.map_apply]
  exact uScal_pow_fix hQ τ hτQ _ (uScal_rotMat_entry a b x y)

theorem uScal_rotMat_unitary {Q : ℕ} (hQ : Q ≠ 0) (τ : K ≃+* K) (hτQ : ∀ x, τ x = x ^ Q)
    (a b : Fin d) : ((uScal_rotMat (K := K) a b).map (· ^ Q))ᵀ * uScal_rotMat a b = 1 := by
  rw [uScal_rotMat_map hQ τ hτQ, uScal_rotMat, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.transpose_swap]
  have hDD : Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1) *
      Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    split_ifs <;> norm_num
  calc Matrix.swap K a b * Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1) *
        (Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1) * Matrix.swap K a b)
      = Matrix.swap K a b * (Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1) *
          Matrix.diagonal (fun k : Fin d => if k = a then (-1 : K) else 1)) *
          Matrix.swap K a b := by
        simp only [mul_assoc]
    _ = 1 := by rw [hDD, mul_one, Matrix.swap_mul_self]

@[expose] noncomputable def uScal_rotGL (a b : Fin d) (hab : a ≠ b) : GL (Fin d) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uScal_rotMat (K := K) a b)
    (by rw [uScal_det_rotMat hab]; exact one_ne_zero)

theorem uScal_rotGL_val {a b : Fin d} (hab : a ≠ b) :
    (uScal_rotGL (K := K) a b hab : Matrix (Fin d) (Fin d) K) = uScal_rotMat a b :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem uScal_rotGL_mem {Q : ℕ} (hQ : Q ≠ 0) (τ : K ≃+* K) (hτQ : ∀ x, τ x = x ^ Q) {a b : Fin d}
    (hab : a ≠ b) : uScal_rotGL (K := K) a b hab ∈ StatedSU d Q K :=
  uScal_mem_of_unitary Q _ (by rw [uScal_rotGL_val, uScal_det_rotMat hab])
    (by rw [uScal_rotGL_val]; exact uScal_rotMat_unitary hQ τ hτQ a b)

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
