module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Levi2

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def uEl (t : K) : SL(2, K) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lEl (s : K) : SL(2, K) := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

theorem uEl_inv (t : K) : (uEl t)⁻¹ = uEl (-t) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uEl, Matrix.mul_apply, Fin.sum_univ_two]

theorem lEl_inv (s : K) : (lEl s)⁻¹ = lEl (-s) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lEl, Matrix.mul_apply, Fin.sum_univ_two]

theorem leviDual_uEl (h : UnitaryFieldData p f K) (t : K) :
    leviDual h (SpecialLinearGroup.toGL (uEl t)) = !![1, 0; -h.bar t, 1] := by
  rw [leviDual, ← map_inv, uEl_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uEl]

theorem leviDual_lEl (h : UnitaryFieldData p f K) (s : K) :
    leviDual h (SpecialLinearGroup.toGL (lEl s)) = !![1, -h.bar s; 0, 1] := by
  rw [leviDual, ← map_inv, lEl_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lEl]

noncomputable abbrev leviMat (h : UnitaryFieldData p f K) (A : SL(2, K)) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  (((leviSU h 0 A : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)

theorem leviMat_ee (h : UnitaryFieldData p f K) (A : SL(2, K)) (i j : Fin 2) :
    leviMat h A (Sum.inl i) (Sum.inl j) = (A : Matrix (Fin 2) (Fin 2) K) i j := by
  simp only [leviMat, coe_leviSU, coe_leviGL]
  rfl

theorem leviMat_ff (h : UnitaryFieldData p f K) (A : SL(2, K)) (i j : Fin 2) :
    leviMat h A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) =
      leviDual h (SpecialLinearGroup.toGL A) i j := by
  simp only [leviMat, coe_leviSU, coe_leviGL]
  rfl

theorem leviMat_ef (h : UnitaryFieldData p f K) (A : SL(2, K)) (i j : Fin 2) :
    leviMat h A (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
  simp only [leviMat, coe_leviSU, coe_leviGL]
  rfl

theorem leviMat_fe (h : UnitaryFieldData p f K) (A : SL(2, K)) (i j : Fin 2) :
    leviMat h A (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
  simp only [leviMat, coe_leviSU, coe_leviGL]
  rfl

theorem uEl_00 (t : K) : (uEl t : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by simp [uEl]
theorem uEl_01 (t : K) : (uEl t : Matrix (Fin 2) (Fin 2) K) 0 1 = t := by simp [uEl]
theorem uEl_10 (t : K) : (uEl t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp [uEl]
theorem uEl_11 (t : K) : (uEl t : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simp [uEl]
theorem lEl_00 (s : K) : (lEl s : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by simp [lEl]
theorem lEl_01 (s : K) : (lEl s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp [lEl]
theorem lEl_10 (s : K) : (lEl s : Matrix (Fin 2) (Fin 2) K) 1 0 = s := by simp [lEl]
theorem lEl_11 (s : K) : (lEl s : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simp [lEl]

theorem dualU_00 (h : UnitaryFieldData p f K) (t : K) :
    leviDual h (SpecialLinearGroup.toGL (uEl t)) 0 0 = 1 := by rw [leviDual_uEl]; simp
theorem dualU_01 (h : UnitaryFieldData p f K) (t : K) :
    leviDual h (SpecialLinearGroup.toGL (uEl t)) 0 1 = 0 := by rw [leviDual_uEl]; simp
theorem dualU_10 (h : UnitaryFieldData p f K) (t : K) :
    leviDual h (SpecialLinearGroup.toGL (uEl t)) 1 0 = -h.bar t := by rw [leviDual_uEl]; simp
theorem dualU_11 (h : UnitaryFieldData p f K) (t : K) :
    leviDual h (SpecialLinearGroup.toGL (uEl t)) 1 1 = 1 := by rw [leviDual_uEl]; simp
theorem dualL_00 (h : UnitaryFieldData p f K) (s : K) :
    leviDual h (SpecialLinearGroup.toGL (lEl s)) 0 0 = 1 := by rw [leviDual_lEl]; simp
theorem dualL_01 (h : UnitaryFieldData p f K) (s : K) :
    leviDual h (SpecialLinearGroup.toGL (lEl s)) 0 1 = -h.bar s := by rw [leviDual_lEl]; simp
theorem dualL_10 (h : UnitaryFieldData p f K) (s : K) :
    leviDual h (SpecialLinearGroup.toGL (lEl s)) 1 0 = 0 := by rw [leviDual_lEl]; simp
theorem dualL_11 (h : UnitaryFieldData p f K) (s : K) :
    leviDual h (SpecialLinearGroup.toGL (lEl s)) 1 1 = 1 := by rw [leviDual_lEl]; simp

theorem levi_u_e0 (h : UnitaryFieldData p f K) (t : K) (v : HypIndex 2 0 → K) :
    (leviMat h (uEl t) *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) + t * v (Sum.inl 1) := by
  rw [leviSU_mulVec, leviDual_uEl]
  simp [leviFun, uEl, dotProduct, Fin.sum_univ_two]

theorem levi_u_e1 (h : UnitaryFieldData p f K) (t : K) (v : HypIndex 2 0 → K) :
    (leviMat h (uEl t) *ᵥ v) (Sum.inl 1) = v (Sum.inl 1) := by
  rw [leviSU_mulVec, leviDual_uEl]
  simp [leviFun, uEl, dotProduct, Fin.sum_univ_two]

theorem levi_u_f0 (h : UnitaryFieldData p f K) (t : K) (v : HypIndex 2 0 → K) :
    (leviMat h (uEl t) *ᵥ v) (Sum.inr (Sum.inr 0)) = v (Sum.inr (Sum.inr 0)) := by
  rw [leviSU_mulVec, leviDual_uEl]
  simp [leviFun, uEl, dotProduct, Fin.sum_univ_two]

theorem levi_u_f1 (h : UnitaryFieldData p f K) (t : K) (v : HypIndex 2 0 → K) :
    (leviMat h (uEl t) *ᵥ v) (Sum.inr (Sum.inr 1)) =
      -h.bar t * v (Sum.inr (Sum.inr 0)) + v (Sum.inr (Sum.inr 1)) := by
  rw [leviSU_mulVec, leviDual_uEl]
  simp [leviFun, uEl, dotProduct, Fin.sum_univ_two]

theorem levi_l_e0 (h : UnitaryFieldData p f K) (s : K) (v : HypIndex 2 0 → K) :
    (leviMat h (lEl s) *ᵥ v) (Sum.inl 0) = v (Sum.inl 0) := by
  rw [leviSU_mulVec, leviDual_lEl]
  simp [leviFun, lEl, dotProduct, Fin.sum_univ_two]

theorem levi_l_e1 (h : UnitaryFieldData p f K) (s : K) (v : HypIndex 2 0 → K) :
    (leviMat h (lEl s) *ᵥ v) (Sum.inl 1) = s * v (Sum.inl 0) + v (Sum.inl 1) := by
  rw [leviSU_mulVec, leviDual_lEl]
  simp [leviFun, lEl, dotProduct, Fin.sum_univ_two]

theorem levi_l_f0 (h : UnitaryFieldData p f K) (s : K) (v : HypIndex 2 0 → K) :
    (leviMat h (lEl s) *ᵥ v) (Sum.inr (Sum.inr 0)) =
      v (Sum.inr (Sum.inr 0)) + -h.bar s * v (Sum.inr (Sum.inr 1)) := by
  rw [leviSU_mulVec, leviDual_lEl]
  simp [leviFun, lEl, dotProduct, Fin.sum_univ_two]

theorem levi_l_f1 (h : UnitaryFieldData p f K) (s : K) (v : HypIndex 2 0 → K) :
    (leviMat h (lEl s) *ᵥ v) (Sum.inr (Sum.inr 1)) = v (Sum.inr (Sum.inr 1)) := by
  rw [leviSU_mulVec, leviDual_lEl]
  simp [leviFun, lEl, dotProduct, Fin.sum_univ_two]

end Levi2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
