module

public import CFSG.Timmesfeld.ARS.CaseHTF

public section

namespace CFSG.CGT.T75O

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH

variable {G : Type} [Group G] {R : Set (Subgroup G)}
  {A A₀ P P' : Subgroup G} {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E]
  (c : Coords S F E) [CharP E 2] [CharP F 2] [Finite F] (e : F →+* E)
  (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)

namespace Apt

include he in
theorem fixed_conditions {u : F} {w r : E} {v : F}
    (h : ∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) (s : E) :
    e u * s = 0 ∧ e u * c.sharp s + c.F3 s w = 0 ∧
      u * c.N s + c.F2 s w + c.T s r = 0 := by
  have := S.hyp.finite
  have h1 := h s
  rw [c.ad_x1 e he] at h1
  obtain ⟨-, h2, h3, h4⟩ := c.vc_injective h1
  refine ⟨by simpa using h2, ?_, ?_⟩
  · linear_combination h3
  · linear_combination h4

include he in
theorem fixed_u {u : F} {w r : E} {v : F}
    (h : ∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) : u = 0 := by
  have := (fixed_conditions c e he h 1).1
  rw [mul_one] at this
  exact (map_eq_zero e).1 this

end Apt

variable [Finite E] {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))

include he hτ0 hτ in
theorem hfix_g2 (hsq : ∀ s, c.sharp s = s ^ 2) (hω : ∃ ω : E, ω ≠ 0 ∧ ω ≠ 1) :
    ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0 := by
  intro u w r v h
  obtain ⟨-, -, hF2, hT⟩ := c.G2_structure e he hτ0 hτ hsq
  have hu : u = 0 := Apt.fixed_u c e he h
  subst hu
  have key : ∀ s : E, s ^ 2 * w + s * r = 0 := fun s => by
    have h1 := (Apt.fixed_conditions c e he h s).2.2
    rw [zero_mul, zero_add] at h1
    have h2 : e (τ⁻¹ * (c.F2 s w + c.T s r)) = 0 := by rw [h1, mul_zero, map_zero]
    rwa [mul_add, map_add, hF2, hT] at h2
  obtain ⟨ω, hω0, hω1⟩ := hω
  have e1 := key 1
  have e2 := key ω
  have e3 : ω * (ω - 1) * w = 0 := by linear_combination e2 - ω * e1
  have hw : w = 0 := by
    rcases mul_eq_zero.1 e3 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hω0
      · exact absurd (sub_eq_zero.1 h4) hω1
    · exact h3
  refine ⟨rfl, hw, ?_⟩
  rw [hw] at e1
  linear_combination e1

include he hτ0 hτ in
theorem hfix_d4 (σ : E →+* E) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hsq : ∀ s, c.sharp s = σ s * σ (σ s)) (hs : ∃ s : E, σ s ≠ s) :
    ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0 := by
  intro u w r v h
  obtain ⟨-, hF3, hF2, hT⟩ := c.D4_structure e he hτ0 hτ σ hσ3 hsq
  have hu : u = 0 := Apt.fixed_u c e he h
  subst hu
  have hw : w = 0 := by
    have hcr : ∀ s : E, σ s * σ (σ w) + σ (σ s) * σ w = 0 := fun s => by
      have h1 := (Apt.fixed_conditions c e he h s).2.1
      rw [map_zero, zero_mul, zero_add, hF3] at h1
      exact h1
    have h1 := hcr 1
    simp only [map_one, one_mul] at h1
    have h2 : σ (σ w) = σ w := by
      have := eq_neg_of_add_eq_zero_left h1
      rwa [CharTwo.neg_eq] at this
    have h3 : σ w = w := by
      have h4 := congrArg σ h2
      rw [hσ3] at h4
      exact h2.symm.trans h4.symm
    have h5 : σ (σ w) = w := h2.trans h3
    by_contra hw0
    obtain ⟨s, hs⟩ := hs
    have h6 := hcr s
    rw [h5, h3] at h6
    have h7 : (σ s + σ (σ s)) * w = 0 := by linear_combination h6
    rcases mul_eq_zero.1 h7 with h8 | h8
    · apply hs
      have := eq_neg_of_add_eq_zero_left h8
      rw [CharTwo.neg_eq] at this
      exact (σ.injective this).symm
    · exact hw0 h8
  subst hw
  refine ⟨rfl, rfl, ?_⟩
  by_contra hr0
  have h1 := (Apt.fixed_conditions c e he h r⁻¹).2.2
  rw [zero_mul, zero_add] at h1
  have h2 : e (τ⁻¹ * (c.F2 r⁻¹ 0 + c.T r⁻¹ r)) = 0 := by rw [h1, mul_zero, map_zero]
  rw [mul_add, map_add, hF2, hT, mul_zero, inv_mul_cancel₀ hr0] at h2
  have h3 : (1 : E) + 1 + 1 = 0 := by simpa [trace3] using h2
  rw [CharTwo.add_self_eq_zero, zero_add] at h3
  exact one_ne_zero h3

end CFSG.CGT.T75O
