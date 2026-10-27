module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityRegular
public import CFSG.LieType.SeitzGeneration.OrthSdMixing

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

section Pairing

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M]

theorem exists_aniso_of_pairing {bar : E →+* E} (hbar : ∃ z, bar z ≠ z) (h2 : (2 : E) = 0)
    {H : M → M → E} (hadd₁ : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₁ : ∀ (c : E) u w, H (c • u) w = bar c * H u w)
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) (hsymm : ∀ u w, H w u = bar (H u w))
    {u u' : M} (h : H u u' ≠ 0) :
    H u u ≠ 0 ∨ H u' u' ≠ 0 ∨ ∃ c : E, H (u + c • u') (u + c • u') ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h1', h3⟩ := hcon
  obtain ⟨z, hz⟩ := hbar
  have hcm : z * (H u u')⁻¹ * H u u' = z := by field_simp
  have h4 := h3 (z * (H u u')⁻¹)
  simp only [hadd₁, hadd₂, hsm₁, hsm₂, h1, h1', hsymm u u', mul_zero, zero_add] at h4
  have h5 : z * (H u u')⁻¹ * H u u' + bar (z * (H u u')⁻¹ * H u u') = 0 := by
    rw [map_mul]
    linear_combination h4
  rw [hcm] at h5
  exact hz (by linear_combination h5 - z * h2)

end Pairing

section Mixing

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_selfdual_mixing_action_even (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp5 : 5 ≤ p) {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) (h2 : (2 : K) = 0) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ v ∈ S₁, x v ∈ S₁) (hS₂ : ∀ v ∈ S₂, x v ∈ S₂)
    (hnd₁ : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S₁).Nondegenerate)
    (hnd₂ : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S₂).Nondegenerate)
    (hperp : ∀ u ∈ S₁, ∀ w ∈ S₂, QuadraticMap.polar Q u w = 0)
    (hv : S₁ ⊓ primaryComponent x.toLinearMap r ≠ ⊥)
    (hw : S₂ ⊓ primaryComponent x.toLinearMap r ≠ ⊥) :
    ∃ g ∈ specialBlock Q x r, ∃ u w : primaryComponent x.toLinearMap r,
      (u : V) ∈ S₁ ∧ (w : V) ∈ S₂ ∧ u ≠ 0 ∧ w ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x r u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x r w)) ∧
      ∃ lam mu : AdjoinRoot r, lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ z : AdjoinRoot r,
        g (eline x r u z) = eline x r u (lam * z) + eline x r w (mu * z) := by
  have : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  have h2E : (2 : AdjoinRoot r) = 0 := by
    have h4 : algebraMap K (AdjoinRoot r) 2 = 2 := map_ofNat _ 2
    rw [← h4, h2, map_zero]
  have hneg : ∀ z : AdjoinRoot r, -z = z := fun z => by linear_combination (-z) * h2E
  obtain ⟨f₁, hf₁fix, hf₁0, hf₁1⟩ :
      ∃ f₁ : AdjoinRoot r, hU.bar f₁ = f₁ ∧ f₁ ≠ 0 ∧ f₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set hU.fixedField) ⊆ {0, 1} := by
      intro y _
      by_cases hy : (y : AdjoinRoot r) = 0
      · exact Or.inl (Subtype.ext hy)
      · exact Or.inr (Subtype.ext (hcon y (hU.mem_fixedField.mp y.2) hy))
    have hle : Nat.card hU.fixedField ≤ 2 := by
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at h1
      exact h1.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    have h1 := hx.p_lt_card_adjoinRoot hp hr hne1
    have h3 : Nat.card (AdjoinRoot r) = Nat.card hU.fixedField ^ 2 := by
      rw [hU.card, hU.card_fixedField, ← pow_mul, mul_comm]
    have h4 : Nat.card hU.fixedField ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have hAn : ∀ {S : Submodule K V}, (∀ v ∈ S, x v ∈ S) →
      (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S).Nondegenerate →
      S ⊓ primaryComponent x.toLinearMap r ≠ ⊥ →
      ∃ y : primaryComponent x.toLinearMap r, (y : V) ∈ S ∧ H y y ≠ 0 := by
    intro S hS hnd hne
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨v', hv', hpol⟩ := exists_polar_ne_zero_of_selfdual hx hr hself hS hnd hv hv0
    have hHu : H ⟨v, hv.2⟩ ⟨v', hv'.2⟩ ≠ 0 := fun h0 => hpol (by
      have := htr ⟨v, hv.2⟩ ⟨v', hv'.2⟩ 1
      rw [h0, zero_mul, map_zero, one_smul] at this
      exact this.symm)
    rcases exists_aniso_of_pairing hU.exists_bar_ne h2E hadd₁ hadd₂ hsm₁' hsm₂ hsymm' hHu with
      h | h | ⟨c, h⟩
    · exact ⟨_, hv.1, h⟩
    · exact ⟨_, hv'.1, h⟩
    · exact ⟨_, S.add_mem hv.1 (smul_mem_of_stable hS c ⟨v', hv'.2⟩ hv'.1), h⟩
  obtain ⟨u, hu1, hHuu⟩ := hAn hS₁ hnd₁ hv
  obtain ⟨w', hw1, hHww⟩ := hAn hS₂ hnd₂ hw
  have hH0 : ∀ y : primaryComponent x.toLinearMap r, y = 0 → H y y = 0 := fun y hy => by
    rw [hy]
    simpa using hsm₁' 0 0 0
  have hu0 : u ≠ 0 := fun h => hHuu (hH0 u h)
  have hw0 : w' ≠ 0 := fun h => hHww (hH0 w' h)
  have hHuw : H u w' = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w' c]
    exact hperp _ hu1 _ (smul_mem_of_stable hS₂ c w' hw1)
  have hHwu : H w' u = 0 := by rw [hsymm' u w', hHuw, map_zero]
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w' w') = H w' w' := (hsymm' w' w').symm
  have hreg : ∀ y : primaryComponent x.toLinearMap r, H y y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) := by
    intro y hy
    rintro _ ⟨z₁, rfl⟩ hxy
    have hz : ∀ z : AdjoinRoot r, Algebra.trace K (AdjoinRoot r) (hU.bar z₁ * H y y * z) = 0 := by
      intro z
      have h1 := hxy (eline x r y z) ⟨z, rfl⟩
      rw [eline_apply, eline_apply] at h1
      have h3 := htr (z₁ • y) y z
      rw [hsm₁', h1] at h3
      exact h3
    have h4 : hU.bar z₁ * H y y = 0 := eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) hz
    have h5 : hU.bar z₁ = 0 := (mul_eq_zero.mp h4).resolve_right hy
    have h6 : z₁ = 0 := by
      have := congrArg hU.bar h5
      rwa [hU.bar_bar, map_zero] at this
    rw [h6, map_zero]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : AdjoinRoot r, f₀ = -(H u u) / H w' w' := ⟨_, rfl⟩
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀]
    exact div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w') (u + c • w') = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w' w') = f₀ * H w' w' := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  obtain ⟨a, ha⟩ : ∃ a : AdjoinRoot r, a = f₁ * (H u u)⁻¹ := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero hf₁0 (inv_ne_zero hHuu)
  have haσ : hU.bar a = -a := by
    rw [ha, map_mul, map_inv₀, hHuu_fix, hf₁fix, hneg]
  have haH : a * H u u = f₁ := by rw [ha, mul_assoc, inv_mul_cancel₀ hHuu, mul_one]
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hlam : 1 + a * H u u ≠ 0 := by
    rw [haH]
    intro h0
    exact hf₁1 (by linear_combination h0 - h2E)
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + a * H u u) * z) • u + ((a * H u u * c) * z) • w' := by
    intro z
    have hHe : H (u + c • w') (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe]
    module
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, u, w', hu1, hw1, hu0, hw0, hreg u hHuu,
    hreg w' hHww, 1 + a * H u u, a * H u u * c, hlam,
    mul_ne_zero (mul_ne_zero ha0 hHuu) hc0, fun z => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm

end Mixing

end CFSG.LieType.SeitzGeneration.OrthBlk
