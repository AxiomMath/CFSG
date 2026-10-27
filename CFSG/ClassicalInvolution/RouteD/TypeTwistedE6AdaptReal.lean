module

public import CFSG.ClassicalInvolution.Phan.Geometry.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan Module

structure RealStr {K : Type*} [Field K] (σ : K ≃+* K) (m : ℕ) where
  τ : (Fin m → K) → (Fin m → K)
  map_add : ∀ u w, τ (u + w) = τ u + τ w
  map_smul : ∀ (c : K) (u : Fin m → K), τ (c • u) = σ c • τ u
  invol : ∀ u, τ (τ u) = u
  herm_τ : ∀ u w, herm σ (τ u) (τ w) = σ (herm σ u w)

namespace RealStr

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ} (T : RealStr σ m)

@[expose] def IsReal (u : Fin m → K) : Prop := T.τ u = u

@[expose] def IsStable (U : Submodule K (Fin m → K)) : Prop := ∀ u ∈ U, T.τ u ∈ U

theorem τ_zero : T.τ 0 = 0 := by
  have h := T.map_add 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem τ_neg (u : Fin m → K) : T.τ (-u) = -T.τ u := by
  have h := T.map_add u (-u)
  rw [add_neg_cancel, T.τ_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem τ_sub (u w : Fin m → K) : T.τ (u - w) = T.τ u - T.τ w := by
  rw [sub_eq_add_neg, T.map_add, T.τ_neg, ← sub_eq_add_neg]

theorem isReal_add_real {u w : Fin m → K} (hu : T.IsReal u) (hw : T.IsReal w) :
    T.IsReal (u + w) := by
  unfold IsReal at *
  rw [T.map_add, hu, hw]

theorem herm_real {u w : Fin m → K} (hu : T.IsReal u) (hw : T.IsReal w) :
    σ (herm σ u w) = herm σ u w := by
  have := T.herm_τ u w
  rw [hu, hw] at this
  exact this.symm

theorem exists_decomp (h2 : (2 : K) ≠ 0) {δ : K} (hδ : σ δ = -δ) (hδ0 : δ ≠ 0)
    (u : Fin m → K) :
    ∃ r₁ r₂ : Fin m → K, T.IsReal r₁ ∧ T.IsReal r₂ ∧ u = r₁ + δ • r₂ ∧
      ∀ U : Submodule K (Fin m → K), T.IsStable U → u ∈ U → r₁ ∈ U ∧ r₂ ∈ U := by
  have h2i : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ0
  refine ⟨(2 : K)⁻¹ • (u + T.τ u), ((2 : K)⁻¹ * δ⁻¹) • (u - T.τ u), ?_, ?_, ?_, ?_⟩
  · unfold IsReal
    rw [T.map_smul, T.map_add, T.invol, add_comm]
    have : σ (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat σ 2]
    rw [this]
  · unfold IsReal
    rw [T.map_smul, T.τ_sub, T.invol]
    have : σ ((2 : K)⁻¹ * δ⁻¹) = -((2 : K)⁻¹ * δ⁻¹) := by
      rw [map_mul, map_inv₀, map_inv₀, hδ, map_ofNat σ 2, inv_neg, mul_neg]
    rw [this, neg_smul, ← smul_neg, neg_sub]
  · have e : δ • (((2 : K)⁻¹ * δ⁻¹) • (u - T.τ u)) = (2 : K)⁻¹ • (u - T.τ u) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [e, ← smul_add]
    have : u + T.τ u + (u - T.τ u) = (2 : K) • u := by module
    rw [this, smul_smul, h2i, one_smul]
  · intro U hU hu
    have hτ := hU u hu
    exact ⟨U.smul_mem _ (U.add_mem hu hτ), U.smul_mem _ (U.sub_mem hu hτ)⟩

theorem isStable_perp {U : Submodule K (Fin m → K)} (hst : T.IsStable U) :
    T.IsStable (perp σ U) := by
  intro u hu s hs
  have h1 := T.herm_τ u (T.τ s)
  rw [T.invol] at h1
  have h2 : herm σ u (T.τ s) = 0 := hu _ (hst s hs)
  rw [h2, map_zero] at h1
  exact h1

section Aniso

variable (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)

include hσ h2

theorem exists_real_aniso {U : Submodule K (Fin m → K)} (hU : Nondeg σ U) (hne : U ≠ ⊥)
    (hst : T.IsStable U) : ∃ r ∈ U, T.IsReal r ∧ herm σ r r ≠ 0 := by
  by_contra H
  push Not at H
  obtain ⟨δ, hδ0, hδ⟩ := hσ.exists_traceZero
  have hδσ : σ δ = -δ := eq_neg_of_add_eq_zero_right hδ
  have hreal : ∀ r ∈ U, ∀ r' ∈ U, T.IsReal r → T.IsReal r' → herm σ r r' = 0 := by
    intro r hr r' hr' hrr hrr'
    have h1 := H (r + r') (U.add_mem hr hr') (T.isReal_add_real hrr hrr')
    rw [herm_add_left, herm_add_right, herm_add_right, H r hr hrr, H r' hr' hrr', zero_add,
      add_zero] at h1
    have hc : herm σ r' r = herm σ r r' := by
      rw [herm_conj σ hσ.invol r r', T.herm_real hrr hrr']
    rw [hc] at h1
    have h3 : (2 : K) * herm σ r r' = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hzero : ∀ u ∈ U, ∀ w ∈ U, herm σ u w = 0 := by
    intro u hu w hw
    obtain ⟨r₁, r₂, hr₁, hr₂, rfl, hmem⟩ := T.exists_decomp h2 hδσ hδ0 u
    obtain ⟨r₁', r₂', hr₁', hr₂', rfl, hmem'⟩ := T.exists_decomp h2 hδσ hδ0 w
    obtain ⟨h1U, h2U⟩ := hmem U hst hu
    obtain ⟨h1U', h2U'⟩ := hmem' U hst hw
    rw [herm_add_left, herm_smul_left, herm_add_right, herm_add_right, herm_smul_right,
      herm_smul_right, hreal _ h1U _ h1U' hr₁ hr₁', hreal _ h1U _ h2U' hr₁ hr₂',
      hreal _ h2U _ h1U' hr₂ hr₁', hreal _ h2U _ h2U' hr₂ hr₂']
    ring
  obtain ⟨s, hsU, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact hs0 (hU s hsU fun t ht => hzero s hsU t ht)

omit hσ h2 in
theorem isStable_inf_perp {U : Submodule K (Fin m → K)} (hst : T.IsStable U) {e : Fin m → K}
    (he : T.IsReal e) : T.IsStable (U ⊓ perp σ (K ∙ e)) := by
  intro u hu
  refine ⟨hst u hu.1, mem_perp_span_singleton.mpr ?_⟩
  have h0 : herm σ u e = 0 := mem_perp_span_singleton.mp hu.2
  have := T.herm_τ u e
  rw [he, h0, map_zero] at this
  exact this

theorem exists_real_orth_triple {U : Submodule K (Fin m → K)} (hU : Nondeg σ U)
    (hst : T.IsStable U) (hdim : 3 ≤ finrank K U) :
    ∃ e₁ e₂ e₃ : Fin m → K, (e₁ ∈ U ∧ T.IsReal e₁ ∧ herm σ e₁ e₁ ≠ 0) ∧
      (e₂ ∈ U ∧ T.IsReal e₂ ∧ herm σ e₂ e₂ ≠ 0) ∧ (e₃ ∈ U ∧ T.IsReal e₃ ∧ herm σ e₃ e₃ ≠ 0) ∧
      herm σ e₁ e₂ = 0 ∧ herm σ e₁ e₃ = 0 ∧ herm σ e₂ e₃ = 0 := by
  have hne : U ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨e₁, he₁U, he₁R, he₁⟩ := T.exists_real_aniso hσ h2 hU hne hst
  have hU₂ : Nondeg σ (U ⊓ perp σ (K ∙ e₁)) := Nondeg.inf_perp_span_singleton hσ he₁U he₁ hU
  have hd₂ := finrank_eq_inf_perp_add_one hσ he₁U he₁
  have hst₂ := T.isStable_inf_perp hst he₁R
  have hne₂ : U ⊓ perp σ (K ∙ e₁) ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hd₂
    omega
  obtain ⟨e₂, he₂U, he₂R, he₂⟩ := T.exists_real_aniso hσ h2 hU₂ hne₂ hst₂
  have hU₃ : Nondeg σ (U ⊓ perp σ (K ∙ e₁) ⊓ perp σ (K ∙ e₂)) :=
    Nondeg.inf_perp_span_singleton hσ he₂U he₂ hU₂
  have hd₃ := finrank_eq_inf_perp_add_one hσ he₂U he₂
  have hst₃ := T.isStable_inf_perp hst₂ he₂R
  have hne₃ : U ⊓ perp σ (K ∙ e₁) ⊓ perp σ (K ∙ e₂) ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hd₃
    omega
  obtain ⟨e₃, he₃U, he₃R, he₃⟩ := T.exists_real_aniso hσ h2 hU₃ hne₃ hst₃
  refine ⟨e₁, e₂, e₃, ⟨he₁U, he₁R, he₁⟩, ⟨he₂U.1, he₂R, he₂⟩, ⟨he₃U.1.1, he₃R, he₃⟩, ?_, ?_, ?_⟩
  · exact (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp he₂U.2)
  · exact (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp he₃U.1.2)
  · exact (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp he₃U.2)

end Aniso

end RealStr

end CFSG.ClassicalInvolution.RouteD.NonClassical
