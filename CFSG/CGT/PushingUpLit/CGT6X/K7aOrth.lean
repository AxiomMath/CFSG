module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix

section Orth

variable (F : Type*) [Field F]

variable {F} in
theorem coe_inv_eq_transpose {A : SpecialLinearGroup (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1) :
    ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  calc ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ) := by
        rw [hA, Matrix.mul_one]
    _ = (((A⁻¹ * A : SpecialLinearGroup (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
        rw [SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
    _ = (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
        rw [inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mul]

@[expose] def orthSL : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1}
  mul_mem' := by
    intro A B hA hB
    have hA' : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := hA
    have hB' : (B : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := hB
    show ((A * B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((A * B : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = 1
    rw [SpecialLinearGroup.coe_mul, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (B : Matrix (Fin 3) (Fin 3) F), hB', Matrix.one_mul, hA']
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = 1
    simp
  inv_mem' := by
    intro A hA
    have hA' : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := hA
    have hinv := coe_inv_eq_transpose hA'
    show ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = 1
    rw [hinv, transpose_transpose]
    exact mul_eq_one_comm.mp hA'

variable {F}

theorem mem_orthSL {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ orthSL F ↔ (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 :=
  Iff.rfl

theorem transpose_mul_self_of_mem {A : SpecialLinearGroup (Fin 3) F} (hA : A ∈ orthSL F) :
    (A : Matrix (Fin 3) (Fin 3) F)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 :=
  mul_eq_one_comm.mp hA

end Orth

section CharTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem eq_one_of_sq_eq_one {s : F} (h : s ^ 2 = 1) : s = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (s - 1) ^ 2 = 0 := by linear_combination h + (1 - s) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h0)

theorem sq_add_three (a b c : F) : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (a * b + a * c + b * c) * h2

theorem row_sum_eq_one {M : Matrix (Fin 3) (Fin 3) F} (hM : M * Mᵀ = 1) (i : Fin 3) :
    M i 0 + M i 1 + M i 2 = 1 := by
  apply eq_one_of_sq_eq_one
  have h := congrFun (congrFun hM i) i
  simp only [Matrix.mul_apply, Fin.sum_univ_three, transpose_apply, Matrix.one_apply_eq] at h
  rw [sq_add_three]
  linear_combination h

theorem col_sum_eq_one {M : Matrix (Fin 3) (Fin 3) F} (hM : Mᵀ * M = 1) (j : Fin 3) :
    M 0 j + M 1 j + M 2 j = 1 := by
  apply eq_one_of_sq_eq_one
  have h := congrFun (congrFun hM j) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, transpose_apply, Matrix.one_apply_eq] at h
  rw [sq_add_three]
  linear_combination h

@[expose] def restr (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0 + M 0 1, M 0 1 + M 0 2; M 2 0 + M 2 1, M 2 1 + M 2 2]

omit [CharP F 2] in
theorem restr_one : restr (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [restr]

theorem restr_mul (M N : Matrix (Fin 3) (Fin 3) F) (hN : ∀ j, N 0 j + N 1 j + N 2 j = 1) :
    restr (M * N) = restr M * restr N := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hN0 := hN 0
  have hN1 := hN 1
  have hN2 := hN 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [restr, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Fin.zero_eta,
      Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination (-(M 0 1)) * hN0 + (-(M 0 1)) * hN1 +
      ((M 0 1) * (N 1 0) + (M 0 1) * (N 1 1) - (M 0 1)) * h2
  · linear_combination (-(M 0 1)) * hN1 + (-(M 0 1)) * hN2 +
      ((M 0 1) * (N 1 1) + (M 0 1) * (N 1 2) - (M 0 1)) * h2
  · linear_combination (-(M 2 1)) * hN0 + (-(M 2 1)) * hN1 +
      ((M 2 1) * (N 1 0) + (M 2 1) * (N 1 1) - (M 2 1)) * h2
  · linear_combination (-(M 2 1)) * hN1 + (-(M 2 1)) * hN2 +
      ((M 2 1) * (N 1 1) + (M 2 1) * (N 1 2) - (M 2 1)) * h2

theorem det_restr (M : Matrix (Fin 3) (Fin 3) F) (hr : ∀ i, M i 0 + M i 1 + M i 2 = 1)
    (hc : ∀ j, M 0 j + M 1 j + M 2 j = 1) :
    (restr M).det = M.det := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hc0 := hc 0
  have hc1 := hc 1
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp only [restr, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((-(M 0 0) * (M 1 1) + (M 0 0) + (M 0 1) * (M 1 0) + (M 0 1)) * hr2 +
    ((M 0 0) * (M 1 1) + (M 0 0) * (M 1 2) - (M 0 1) * (M 1 0) - (M 0 1) - (M 0 2) * (M 1 0) -
      (M 0 2)) * hc1 +
    ((M 0 0) * (M 1 1) - (M 0 0) - (M 0 1) * (M 1 0) - (M 0 1) * (M 1 2) - 2 * (M 0 1) +
      (M 0 2) * (M 1 1) - (M 0 2)) * hc0 +
    (-(M 0 0) * (M 1 1) + (M 0 0) + (M 0 1) * (M 1 0) - (M 0 1)) * hr1 +
    (-(M 0 0) * (M 1 1) + (M 0 0) + (M 0 1) * (M 1 0) + (M 0 1) + 2 * (M 1 1) - 2) * hr0 +
    (-2 * (M 0 0) * (M 1 1) + 2 * (M 0 0) + 2 * (M 0 1) * (M 1 0) + (M 1 1) - 1) * h2)

theorem row_sum_of_mem {A : SpecialLinearGroup (Fin 3) F} (hA : A ∈ orthSL F) (i : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) i 0 + (A : Matrix (Fin 3) (Fin 3) F) i 1 +
      (A : Matrix (Fin 3) (Fin 3) F) i 2 = 1 :=
  row_sum_eq_one (mem_orthSL.1 hA) i

theorem col_sum_of_mem {A : SpecialLinearGroup (Fin 3) F} (hA : A ∈ orthSL F) (j : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 j + (A : Matrix (Fin 3) (Fin 3) F) 1 j +
      (A : Matrix (Fin 3) (Fin 3) F) 2 j = 1 :=
  col_sum_eq_one (transpose_mul_self_of_mem hA) j

variable (F) in
@[expose] def orthRestr : orthSL F →* SpecialLinearGroup (Fin 2) F where
  toFun A := ⟨restr (A.1 : Matrix (Fin 3) (Fin 3) F), by
    rw [det_restr _ (row_sum_of_mem A.2) (col_sum_of_mem A.2)]
    exact A.1.2⟩
  map_one' := by
    apply Subtype.ext
    exact restr_one
  map_mul' A B := by
    apply Subtype.ext
    exact restr_mul _ _ (col_sum_of_mem B.2)

theorem orthRestr_injective : Function.Injective (orthRestr F) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hr := row_sum_of_mem A.2
  have hc := col_sum_of_mem A.2
  have hres : restr (A.1 : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg (fun X : SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hA
  have e00 := congrFun (congrFun hres 0) 0
  have e01 := congrFun (congrFun hres 0) 1
  have e10 := congrFun (congrFun hres 1) 0
  have e11 := congrFun (congrFun hres 1) 1
  simp only [restr, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    one_ne_zero] at e00 e01 e10 e11
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hc0 := hc 0
  have hc2 := hc 2
  have h02 : (A.1 : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination hr0 - e00
  have h01 : (A.1 : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination e01 - h02
  have h00 : (A.1 : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by linear_combination e00 - h01
  have h20 : (A.1 : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by linear_combination hr2 - e11
  have h21 : (A.1 : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination e10 - h20
  have h22 : (A.1 : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by linear_combination e11 - h21
  have h10 : (A.1 : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    linear_combination hc0 - h00 - h20
  have h12 : (A.1 : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    linear_combination hc2 - h02 - h22
  have h11 : (A.1 : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by
    linear_combination hr1 - h10 - h12
  apply Subtype.ext
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

theorem card_orthSL_le [Finite F] :
    Nat.card (orthSL F) ≤ Nat.card (SpecialLinearGroup (Fin 2) F) :=
  Nat.card_le_card_of_injective _ orthRestr_injective

end CharTwo

end CFSG.CGT.PushingUpLit.CGT6X.K7a
