module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open Matrix

variable {F : Type*} [Field F]

@[expose] def homR (v w : Fin 3 → F) (c : F) : Matrix (Fin 3) (Fin 3) F :=
  1 + ((c - 1) / 3) • vecMulVec v w

@[expose] def vω (ω : F) : Fin 3 → F := ![1, ω ^ 2, ω]

@[expose] def vωb (ω : F) : Fin 3 → F := ![1, ω, ω ^ 2]

@[expose] def permP : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def dfix (ω s : F) : Matrix (Fin 3) (Fin 3) F :=
  diagonal ![s * (s + 2) / (1 + 2 * s), -ω * s, -ω ^ 2 * s]

@[expose] def xfix (ω s : F) : Matrix (Fin 3) (Fin 3) F :=
  homR (vω ω) (vωb ω) s⁻¹ * dfix ω s * homR (vωb ω) (vω ω) s⁻¹

theorem homR_apply (v w : Fin 3 → F) (c : F) (i j : Fin 3) :
    homR v w c i j = (1 : Matrix (Fin 3) (Fin 3) F) i j + (c - 1) / 3 * (v i * w j) := by
  simp [homR, vecMulVec_apply]

theorem homR_one (v w : Fin 3 → F) : homR v w 1 = 1 := by
  simp [homR]

theorem homR_mul {v w : Fin 3 → F} (h3 : (3 : F) ≠ 0) (hvw : w ⬝ᵥ v = 3) (a b : F) :
    homR v w a * homR v w b = homR v w (a * b) := by
  have hM : vecMulVec v w * vecMulVec v w = (3 : F) • vecMulVec v w := by
    rw [vecMulVec_mul_vecMulVec, hvw, vecMulVec_smul]
  have e : (a * b - 1) / 3 = (a - 1) / 3 + (b - 1) / 3 + 3 * ((a - 1) / 3) * ((b - 1) / 3) := by
    field_simp
    ring
  simp only [homR, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hM]
  rw [e]
  module

theorem transpose_homR (v w : Fin 3 → F) (c : F) : (homR v w c)ᵀ = homR w v c := by
  simp [homR]

theorem map_homR (φ : F →+* F) (v w : Fin 3 → F) (c : F) :
    (homR v w c).map φ = homR (fun i => φ (v i)) (fun i => φ (w i)) (φ c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [homR_apply, map_div₀, map_ofNat]
  · simp [homR_apply, map_div₀, map_ofNat, h]

theorem det_homR {v w : Fin 3 → F} (h3 : (3 : F) ≠ 0) (hvw : w ⬝ᵥ v = 3) (c : F) :
    (homR v w c).det = c := by
  have key : (homR v w c).det = 1 + (c - 1) / 3 * (w ⬝ᵥ v) := by
    rw [det_fin_three]
    simp [homR_apply, dotProduct, Fin.sum_univ_three]
    ring
  rw [key, hvw]
  field_simp
  ring

theorem dot_vωb_vω {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : vωb ω ⬝ᵥ vω ω = 3 := by
  simp [dotProduct, Fin.sum_univ_three, vωb, vω]
  linear_combination (2 * (ω - 1)) * hω

theorem dot_vω_vωb {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : vω ω ⬝ᵥ vωb ω = 3 := by
  simp [dotProduct, Fin.sum_univ_three, vωb, vω]
  linear_combination (2 * (ω - 1)) * hω

theorem permP_mulVec_vω {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : permP *ᵥ vω ω = ω • vω ω := by
  ext i
  fin_cases i
  · simp [permP, vω, mulVec, dotProduct, Fin.sum_univ_three]
  · simp [permP, vω, mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω - 1)) * hω
  · simp [permP, vω, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem vωb_vecMul_permP {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : vωb ω ᵥ* permP = ω • vωb ω := by
  ext i
  fin_cases i
  · simp [permP, vωb, vecMul, dotProduct, Fin.sum_univ_three]
  · simp [permP, vωb, vecMul, dotProduct, Fin.sum_univ_three]
    ring
  · simp [permP, vωb, vecMul, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω - 1)) * hω

theorem permP_mulVec_vωb {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    permP *ᵥ vωb ω = ω ^ 2 • vωb ω := by
  ext i
  fin_cases i
  · simp [permP, vωb, mulVec, dotProduct, Fin.sum_univ_three]
  · simp [permP, vωb, mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω - 1)) * hω
  · simp [permP, vωb, mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω * (ω - 1))) * hω

theorem vω_vecMul_permP {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : vω ω ᵥ* permP = ω ^ 2 • vω ω := by
  ext i
  fin_cases i
  · simp [permP, vω, vecMul, dotProduct, Fin.sum_univ_three]
  · simp [permP, vω, vecMul, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω * (ω - 1))) * hω
  · simp [permP, vω, vecMul, dotProduct, Fin.sum_univ_three]
    linear_combination (-(ω - 1)) * hω

theorem permP_mul_homR_vω {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (c : F) :
    permP * homR (vω ω) (vωb ω) c = homR (vω ω) (vωb ω) c * permP := by
  simp only [homR, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, permP_mulVec_vω hω, vωb_vecMul_permP hω,
    smul_vecMulVec, vecMulVec_smul]

theorem permP_mul_homR_vωb {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (c : F) :
    permP * homR (vωb ω) (vω ω) c = homR (vωb ω) (vω ω) c * permP := by
  simp only [homR, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, permP_mulVec_vωb hω, vω_vecMul_permP hω,
    smul_vecMulVec, vecMulVec_smul]

private theorem xfix_entry (ω s : F) (i j : Fin 3) :
    xfix ω s i j = ∑ k, homR (vω ω) (vωb ω) s⁻¹ i k *
      ![s * (s + 2) / (1 + 2 * s), -ω * s, -ω ^ 2 * s] k * homR (vωb ω) (vω ω) s⁻¹ k j := by
  rw [xfix, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dfix, Matrix.mul_diagonal]

theorem xfix_apply {ω s : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (hs : s ≠ 0)
    (hs2 : 1 + 2 * s ≠ 0) :
    xfix ω s 0 0 = 1 ∧ xfix ω s 1 0 = 0 ∧ xfix ω s 2 0 = 0 ∧
      xfix ω s 1 1 = -ω * (1 + s + s ^ 2) / (1 + 2 * s) ∧
      xfix ω s 2 1 = (s ^ 2 - 1) / (1 + 2 * s) := by
  have hs2' : 1 + s * 2 ≠ 0 := by rwa [mul_comm s 2]
  have h3' : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * h3'
  have h9 : ω ^ 9 = 1 := by linear_combination (ω ^ 6 + ω ^ 3 + 1) * h3'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [xfix_entry] <;>
    simp [Fin.sum_univ_three, homR_apply, vω, vωb] <;> field_simp <;>
    simp only [h3', h6, h9] <;> ring

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
