module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Forms
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Phi
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1

set_option linter.unusedSectionVars false

section Algebra

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

private theorem aux_toRingHom_apply (τ : K ≃+* K) (x : K) : τ.toRingHom x = τ x := rfl

private theorem aux_d_fixed (hA : A2Core σ d q) : σ (d : K) = d :=
  congrArg Units.val hA.fixed

private theorem aux_d_cube (hA : A2Core σ d q) : (d : K) ^ 3 = 1 := by
  have := congrArg Units.val hA.cube
  simpa using this

private theorem aux_char_pos {a : ℕ} (hn : d4Root a (nd 2) = 1) :
    a2Char d (d4Root a) = (d : K) := by
  rw [a2Char, hn, zpow_one]

private theorem aux_char_neg (hA : A2Core σ d q) {a : ℕ} (hn : d4Root a (nd 2) = -1) :
    a2Char d (d4Root a) = (d : K) ^ 2 := by
  have h2 : d⁻¹ = d ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hA.cube)
  rw [a2Char, hn, zpow_neg_one, h2, Units.val_pow_eq_pow_val]

private theorem aux_mu (hA : A2Core σ d q) {μ : Kˣ} (hm : (d : K) * σ (μ : K) = μ) {c : K}
    (hc : σ c = c) : σ ((μ : K) * c) = (d : K) ^ 2 * ((μ : K) * c) := by
  have h3 := aux_d_cube hA
  rw [map_mul, hc]
  linear_combination ((d : K) ^ 2 * c) * hm - (σ (μ : K) * c) * h3

private theorem aux_muinv (hA : A2Core σ d q) {μ : Kˣ} (hm : (d : K) * σ (μ : K) = μ) {c : K}
    (hc : σ c = c) :
    σ (((μ⁻¹ : Kˣ) : K) * c) = (d : K) * (((μ⁻¹ : Kˣ) : K) * c) := by
  have hμ : (μ : K) * ((μ⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 : σ (μ : K) * σ ((μ⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, hμ, map_one]
  rw [map_mul, hc]
  linear_combination (-(c * σ ((μ⁻¹ : Kˣ) : K))) * hμ -
    (c * ((μ⁻¹ : Kˣ) : K) * σ ((μ⁻¹ : Kˣ) : K)) * hm + (c * ((μ⁻¹ : Kˣ) : K) * (d : K)) * e1

private theorem aux_pos (hA : A2Core σ d q) {u : K} (hu : σ u = (d : K) ^ 2 * u) :
    (d : K) * σ u = u ∧ (d : K) * σ (σ u) = σ u ∧ (d : K) * σ (σ (σ u)) = σ (σ u) := by
  have h3 := aux_d_cube hA
  have hd := aux_d_fixed hA
  have e2 : σ (σ u) = (d : K) * u := by
    rw [hu, map_mul, map_pow, hd, hu]
    linear_combination ((d : K) * u) * h3
  have e3 : σ (σ (σ u)) = u := by
    rw [e2, map_mul, hd, hu]
    linear_combination u * h3
  refine ⟨?_, ?_, ?_⟩
  · rw [hu]
    linear_combination u * h3
  · rw [e2, hu]
    ring
  · rw [e3, e2]

private theorem aux_neg (hA : A2Core σ d q) {u : K} (hu : σ u = (d : K) * u) :
    (d : K) ^ 2 * σ u = u ∧ (d : K) ^ 2 * σ (σ u) = σ u ∧
      (d : K) ^ 2 * σ (σ (σ u)) = σ (σ u) := by
  have h3 := aux_d_cube hA
  have hd := aux_d_fixed hA
  have e2 : σ (σ u) = (d : K) ^ 2 * u := by
    rw [hu, map_mul, hd, hu]
    ring
  have e3 : σ (σ (σ u)) = u := by
    rw [e2, map_mul, map_pow, hd, hu]
    linear_combination u * h3
  refine ⟨?_, ?_, ?_⟩
  · rw [hu]
    linear_combination u * h3
  · rw [e2, hu]
    linear_combination ((d : K) * u) * h3
  · rw [e3, e2]

end Algebra


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ} (h : A2Core σ d q)
  (μ : Kˣ) (hm : (d : K) * σ (μ : K) = μ)

private theorem aux_xa3 (hA : A2Core σ d q) {a₀ a₁ a₂ : ℕ} (h₀ : a₀ < 24) (h₁ : a₁ < 24)
    (h₂ : a₂ < 24) {u₀ u₁ u₂ : K} (e₀ : a2Char d (d4Root a₀) * σ u₀ = u₀)
    (e₁ : a2Char d (d4Root a₁) * σ u₁ = u₁) (e₂ : a2Char d (d4Root a₂) * σ u₂ = u₂) :
    a2Conj σ d ((xa a₀ u₀ * xa a₁ u₁ * xa a₂ u₂ : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((xa a₀ u₀ * xa a₁ u₁ * xa a₂ u₂ : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  simp only [Subgroup.coe_mul, a2Conj_mul]
  rw [A2Core.a2Conj_xPar hA (isRoot_d4Root h₀) u₀, A2Core.a2Conj_xPar hA (isRoot_d4Root h₁) u₁,
    A2Core.a2Conj_xPar hA (isRoot_d4Root h₂) u₂, e₀, e₁, e₂]

private theorem aux_W0_mem (τ : K →+* K) : W0 K ∈ twistedGroup τ := by
  have h0 := nHatE_mem (K := K) τ (ng 0)
  rw [nHatE_zero] at h0
  rw [W0, w4_one]
  exact h0

private theorem aux_W1_mem (τ : K →+* K) : W1 K ∈ twistedGroup τ := by
  have h1 := nHatE_mem (K := K) τ (ng 1)
  rw [nHatE_one] at h1
  rw [W1]
  simp only [w4_one]
  exact h1

theorem fix_P1 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fP1 σ.toRingHom h.cube_apply c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fP1 σ.toRingHom h.cube_apply c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  A2Core.a2sl_upper_fixed h hc

theorem fix_M1 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fM1 σ.toRingHom h.cube_apply c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fM1 σ.toRingHom h.cube_apply c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  A2Core.a2sl_lower_fixed h hc

include hm in
theorem fix_P2 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fP2 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fP2 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  obtain ⟨hA, hB, hC⟩ := aux_pos h (aux_mu h hm hc)
  rw [fP2_eq]
  simp only [aux_toRingHom_apply]
  refine aux_xa3 h (by decide) (by decide) (by decide) ?_ ?_ ?_
  · rw [aux_char_pos (by decide +kernel)]
    exact hA
  · rw [aux_char_pos (by decide +kernel)]
    exact hB
  · rw [aux_char_pos (by decide +kernel), map_neg, mul_neg, hC]

include hm in
theorem fix_M2 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fM2 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fM2 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  obtain ⟨hA, hB, hC⟩ := aux_neg h (aux_muinv h hm hc)
  rw [fM2_eq]
  simp only [aux_toRingHom_apply]
  refine aux_xa3 h (by decide) (by decide) (by decide) ?_ ?_ ?_
  · rw [aux_char_neg h (by decide +kernel)]
    exact hA
  · rw [aux_char_neg h (by decide +kernel)]
    exact hB
  · rw [aux_char_neg h (by decide +kernel), map_neg, mul_neg, hC]

include hm in
theorem fix_P3 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fP3 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fP3 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  obtain ⟨hA, hB, hC⟩ := aux_pos h (aux_mu h hm hc)
  rw [fP3_eq]
  simp only [aux_toRingHom_apply]
  refine aux_xa3 h (by decide) (by decide) (by decide) ?_ ?_ ?_
  · rw [aux_char_pos (by decide +kernel), map_neg, mul_neg, hA]
  · rw [aux_char_pos (by decide +kernel), map_neg, mul_neg, hB]
  · rw [aux_char_pos (by decide +kernel), map_neg, mul_neg, hC]

include hm in
theorem fix_M3 (c : K) (hc : σ c = c) :
    a2Conj σ d ((fM3 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((fM3 σ.toRingHom h.cube_apply μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  obtain ⟨hA, hB, hC⟩ := aux_neg h (aux_muinv h hm hc)
  rw [fM3_eq]
  simp only [aux_toRingHom_apply]
  refine aux_xa3 h (by decide) (by decide) (by decide) ?_ ?_ ?_
  · rw [aux_char_neg h (by decide +kernel), map_neg, mul_neg, hA]
  · rw [aux_char_neg h (by decide +kernel), map_neg, mul_neg, hB]
  · rw [aux_char_neg h (by decide +kernel), map_neg, mul_neg, hC]

theorem mem_P1 (c : K) : fP1 σ.toRingHom h.cube_apply c ∈ twistedGroup σ.toRingHom :=
  (slShort σ.toRingHom h.cube_apply (sl2Upper c)).2

theorem mem_M1 (c : K) : fM1 σ.toRingHom h.cube_apply c ∈ twistedGroup σ.toRingHom :=
  (slShort σ.toRingHom h.cube_apply (sl2Lower c)).2

theorem mem_P2 (c : K) : fP2 σ.toRingHom h.cube_apply μ c ∈ twistedGroup σ.toRingHom := by
  unfold fP2
  exact mul_mem (mul_mem (aux_W0_mem _) (mem_P1 h _)) (inv_mem (aux_W0_mem _))

theorem mem_M2 (c : K) : fM2 σ.toRingHom h.cube_apply μ c ∈ twistedGroup σ.toRingHom := by
  unfold fM2
  exact mul_mem (mul_mem (aux_W0_mem _) (mem_M1 h _)) (inv_mem (aux_W0_mem _))

theorem mem_P3 (c : K) : fP3 σ.toRingHom h.cube_apply μ c ∈ twistedGroup σ.toRingHom := by
  unfold fP3
  exact mul_mem (mul_mem (aux_W1_mem _) (mem_P2 h μ _)) (inv_mem (aux_W1_mem _))

theorem mem_M3 (c : K) : fM3 σ.toRingHom h.cube_apply μ c ∈ twistedGroup σ.toRingHom := by
  unfold fM3
  exact mul_mem (mul_mem (aux_W1_mem _) (mem_M2 h μ _)) (inv_mem (aux_W1_mem _))

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
