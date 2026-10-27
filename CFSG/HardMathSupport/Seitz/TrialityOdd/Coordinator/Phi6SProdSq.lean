module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

theorem glConjSL_diagGL_diagGL {F : Type} [Field F] (s : Fˣ) (C : SL(2, F)) :
    glConjSL (diagGL s) (glConjSL (diagGL s) C) = HSL s * C * (HSL s)⁻¹ := by
  apply Subtype.ext
  rw [glConjSL_coe, glConjSL_coe, coe_diagGL_two, coe_diagGL_inv_two,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_HSL, Matrix.adjugate_fin_two,
    Matrix.eta_fin_two (C : Matrix (Fin 2) (Fin 2) F)]
  have hs : (s : F) ≠ 0 := s.ne_zero
  simp only [Matrix.mul_fin_two, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem slLong_mem_invCentGroup (A : SL(2, fixedField σ)) :
    slLong σ hσ A ∈ invCentGroup σ hσ :=
  Subgroup.mem_sup_left ⟨A, rfl⟩

include hσ in
theorem slB_mem_invCentGroup (B : SL(2, K)) : slB σ hσ B ∈ invCentGroup σ hσ :=
  Subgroup.mem_sup_right ⟨B, rfl⟩

include hσ in
theorem sq_mem_invCentGroup_of_mem_TK {t : twistedGroup σ} (ht : t ∈ TK σ) :
    t ^ 2 ∈ invCentGroup σ hσ := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
  have h2 : ∀ C' : SL(2, K), t ^ 2 * slB σ hσ C' * (t ^ 2)⁻¹ =
      slB σ hσ (HSL s * C' * (HSL s)⁻¹) := by
    intro C'
    rw [← glConjSL_diagGL_diagGL, ← hs, ← hs]
    simp only [sq]
    group
  set z : twistedGroup σ := t ^ 2 * (slB σ hσ (HSL s))⁻¹ with hz
  have hzS : z ∈ SProd σ hσ :=
    mul_mem (pow_mem (SProd_mem_of_TK hσ ⟨b, hb⟩) 2) (inv_mem (slB_mem_SProd hσ _))
  have hzc : ∀ C : SL(2, K), z * slB σ hσ C = slB σ hσ C * z := by
    intro C
    have h3 := h2 ((HSL s)⁻¹ * C * HSL s)
    have e : HSL s * ((HSL s)⁻¹ * C * HSL s) * (HSL s)⁻¹ = C := by group
    rw [e, map_mul, map_mul, map_inv] at h3
    rw [hz]
    calc t ^ 2 * (slB σ hσ (HSL s))⁻¹ * slB σ hσ C
        = (t ^ 2 * ((slB σ hσ (HSL s))⁻¹ * slB σ hσ C * slB σ hσ (HSL s)) * (t ^ 2)⁻¹) *
            (t ^ 2 * (slB σ hσ (HSL s))⁻¹) := by group
      _ = slB σ hσ C * (t ^ 2 * (slB σ hσ (HSL s))⁻¹) := by rw [h3]
  obtain ⟨A', hA'⟩ := exists_slLong_of_centralizes_slB hσ hzS hzc
  have ht2 : t ^ 2 = slLong σ hσ A' * slB σ hσ (HSL s) := by
    rw [← hA', hz]
    simp only [sq]
    group
  rw [ht2]
  exact mul_mem (slLong_mem_invCentGroup hσ A') (slB_mem_invCentGroup hσ _)

include hσ in
theorem sq_mem_invCentGroup_of_mem_SProd {x : twistedGroup σ} (hx : x ∈ SProd σ hσ) :
    x ^ 2 ∈ invCentGroup σ hσ := by
  obtain ⟨t, ht, A, B, rfl⟩ := hx
  obtain ⟨A₁, hA₁⟩ := TK_conj_slLong hσ (inv_mem ht) A
  obtain ⟨B₁, hB₁⟩ := TK_conj_slB hσ (inv_mem ht) B
  have e : (t * slLong σ hσ A * slB σ hσ B) ^ 2 =
      t ^ 2 * (slLong σ hσ A₁ * slB σ hσ B₁) * (slLong σ hσ A * slB σ hσ B) := by
    rw [← hA₁, ← hB₁]
    simp only [sq]
    group
  rw [e]
  exact mul_mem (mul_mem (sq_mem_invCentGroup_of_mem_TK hσ ht)
    (mul_mem (slLong_mem_invCentGroup hσ _) (slB_mem_invCentGroup hσ _)))
    (mul_mem (slLong_mem_invCentGroup hσ _) (slB_mem_invCentGroup hσ _))

include hσ in
theorem mem_invCentGroup_of_mem_SProd_of_pow_odd {x : twistedGroup σ} (hx : x ∈ SProd σ hσ)
    {k : ℕ} (hk : x ^ (2 * k + 1) = 1) : x ∈ invCentGroup σ hσ := by
  have hx2 := sq_mem_invCentGroup_of_mem_SProd hσ hx
  have e : x = ((x ^ 2) ^ k)⁻¹ := by
    rw [← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hk
  rw [e]
  exact inv_mem (pow_mem hx2 k)

include hσ in
theorem closure_le_invCentGroup_of_odd {S : Set (twistedGroup σ)}
    (hS : ∀ x ∈ S, x ∈ SProd σ hσ ∧ ∃ k : ℕ, x ^ (2 * k + 1) = 1) :
    Subgroup.closure S ≤ invCentGroup σ hσ :=
  (Subgroup.closure_le _).2 fun x hx =>
    mem_invCentGroup_of_mem_SProd_of_pow_odd hσ (hS x hx).1 (hS x hx).2.choose_spec

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
