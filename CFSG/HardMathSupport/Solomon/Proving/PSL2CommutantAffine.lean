module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Solomon.Proving.PSL2Even

open Matrix

theorem eq_zero_of_kills_basis {F : Type} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) (v w : Fin 2 → F)
    (hD : v 0 * w 1 - v 1 * w 0 ≠ 0)
    (hv : M.mulVec v = 0) (hw : M.mulVec w = 0) : M = 0 := by
  have a0 := congrFun hv 0
  have a1 := congrFun hv 1
  have b0 := congrFun hw 0
  have b1 := congrFun hw 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0 b1
  have h00 : M 0 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination w 1 * a0 - v 1 * b0
  have h01 : M 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination v 0 * b0 - w 0 * a0
  have h10 : M 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination w 1 * a1 - v 1 * b1
  have h11 : M 1 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination v 0 * b1 - w 0 * a1
  have e00 : M 0 0 = 0 := (mul_eq_zero.1 h00).resolve_right hD
  have e01 : M 0 1 = 0 := (mul_eq_zero.1 h01).resolve_right hD
  have e10 : M 1 0 = 0 := (mul_eq_zero.1 h10).resolve_right hD
  have e11 : M 1 1 = 0 := (mul_eq_zero.1 h11).resolve_right hD
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

theorem exists_cyclic_of_not_scalar {F : Type} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (hA : ∀ r : F, A ≠ r • 1) :
    ∃ v : Fin 2 → F, v 0 * (A.mulVec v) 1 - v 1 * (A.mulVec v) 0 ≠ 0 := by
  by_contra h
  have h' : ∀ v : Fin 2 → F, v 0 * (A.mulVec v) 1 - v 1 * (A.mulVec v) 0 = 0 :=
    fun v => by_contra fun hv => h ⟨v, hv⟩
  have h1 := h' ![1, 0]
  have h2 := h' ![0, 1]
  have h3 := h' ![1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h3
  have e10 : A 1 0 = 0 := by linear_combination h1
  have e01 : A 0 1 = 0 := by linear_combination h2
  have e11 : A 1 1 = A 0 0 := by linear_combination h3 - e10 + e01
  apply hA (A 0 0)
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa [Matrix.one_apply] using e01
  · simpa [Matrix.one_apply] using e10
  · simpa [Matrix.one_apply] using e11

theorem affine_of_commute_cyclic {F : Type} [Field F]
    (A B : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F)
    (hΔ : v 0 * (A.mulVec v) 1 - v 1 * (A.mulVec v) 0 ≠ 0)
    (hc : B * A = A * B) :
    ∃ α β : F, B = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
  set w := A.mulVec v with hw
  set Δ := v 0 * w 1 - v 1 * w 0 with hΔdef
  set u := B.mulVec v with hu
  have hBw : B.mulVec w = A.mulVec u := by
    rw [hw, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]
  set α := (u 0 * w 1 - u 1 * w 0) / Δ with hα
  set β := (v 0 * u 1 - v 1 * u 0) / Δ with hβ
  have hu_eq : u = α • v + β • w := by
    funext i
    fin_cases i
    · show u 0 = α * v 0 + β * w 0
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hΔ, hΔdef]
      ring
    · show u 1 = α * v 1 + β * w 1
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hΔ, hΔdef]
      ring
  refine ⟨α, β, ?_⟩
  have hM := eq_zero_of_kills_basis (B - (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A)) v w hΔ ?_ ?_
  · exact sub_eq_zero.1 hM
  · rw [sub_mulVec, add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]
    exact sub_eq_zero.2 hu_eq
  · rw [sub_mulVec, add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec,
      hBw, hu_eq, mulVec_add, mulVec_smul, mulVec_smul, ← hw, sub_self]

theorem mul_comm_of_commute_nonscalar {F : Type} [Field F]
    (A B D : Matrix (Fin 2) (Fin 2) F) (hA : ∀ r : F, A ≠ r • 1)
    (hB : B * A = A * B) (hD : D * A = A * D) : B * D = D * B := by
  obtain ⟨v, hv⟩ := exists_cyclic_of_not_scalar A hA
  obtain ⟨α, β, rfl⟩ := affine_of_commute_cyclic A B v hv hB
  obtain ⟨γ, δ, rfl⟩ := affine_of_commute_cyclic A D v hv hD
  have hPA : Commute (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) A :=
    Commute.add_left ((Commute.one_left A).smul_left α) ((Commute.refl A).smul_left β)
  exact Commute.add_right ((Commute.one_right _).smul_right γ) (hPA.smul_right δ)

end CFSG.HardMathSupport.Solomon.Proving.PSL2Even

end
