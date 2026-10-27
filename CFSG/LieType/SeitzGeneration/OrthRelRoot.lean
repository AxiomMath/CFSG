module

public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthBlk OrthNS

section Rel

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem eichler_mem_of_relRoot {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {U : Submodule K V}
    (hU : PolarNondegOn Q U) {u u' : V} (hu : u ∈ U) (hu' : u' ∈ U) (hQu : Q u = 0)
    (hQu' : Q u' = 0) (hpol : polar Q u u' ≠ 0)
    (hr : ∀ w ∈ U, polar Q u w = 0 → eichler Q u w ∈ H)
    (hr' : ∀ w ∈ U, polar Q u' w = 0 → eichler Q u' w ∈ H) :
    ∀ e ∈ U, ∀ w ∈ U, eichler Q e w ∈ H := by
  classical
  set HU : Subgroup (U ≃ₗ[K] U) := H.comap (extU hU) with hHU
  have hHUO : HU ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) := fun h hh =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y => by
      change Q ((h y : U) : V) = Q (y : V)
      rw [← extU_apply_mem hU h y.2]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hH hh) (y : V)
  have hQU := nondegenerate_comp_subtype hU
  set c := polar Q u u' with hc
  let P : HypPair (Q.comp U.subtype) :=
    ⟨⟨u, hu⟩, ⟨c⁻¹ • u', U.smul_mem _ hu'⟩, hQu, by
      change Q (c⁻¹ • u') = 0
      rw [map_smul_eq_sq, hQu', mul_zero], by
      rw [polar_comp_subtype']
      change polar Q u (c⁻¹ • u') = 1
      rw [polar_smul_right_eq, ← hc, inv_mul_cancel₀ hpol]⟩
  have hmem : ∀ (a : V) (ha : a ∈ U) (w : U), eichler Q a (w : V) ∈ H →
      eichler (Q.comp U.subtype) ⟨a, ha⟩ w ∈ HU := fun a ha w h => by
    change extU hU (eichler (Q.comp U.subtype) ⟨a, ha⟩ w) ∈ H
    rw [extU_eichler]
    exact h
  have hroot : IsRootCenter (Q.comp U.subtype) HU P.e := by
    refine ⟨fun h0 => ?_, hQu, fun w hw => hmem u hu w (hr _ w.2 ?_)⟩
    · have : u = 0 := congrArg Subtype.val h0
      rw [this, polar_zero_left] at hc
      exact hpol hc
    · rw [polar_comp_subtype'] at hw
      exact hw
  have hroot' : IsRootCenter (Q.comp U.subtype) HU P.f := by
    have hc0 : c⁻¹ ≠ 0 := inv_ne_zero hpol
    have h1 : IsRootCenter (Q.comp U.subtype) HU ⟨u', hu'⟩ := by
      refine ⟨fun h0 => ?_, hQu', fun w hw => hmem u' hu' w (hr' _ w.2 ?_)⟩
      · have : u' = 0 := congrArg Subtype.val h0
        rw [this, polar_zero_right] at hc
        exact hpol hc
      · rw [polar_comp_subtype'] at hw
        exact hw
    have := h1.smul hc0
    exact this
  have hle := elementaryGroup_le_of_hypPair hQU hHUO P hroot hroot'
  intro e he w hw
  have h := hle (eichler_mem_elementaryGroup (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩)
  change extU hU (eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩) ∈ H at h
  rwa [extU_eichler] at h

theorem elementaryGroup_le_of_two {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hQ : (polarBilin Q).Nondegenerate)
    {W₁ W₂ : Submodule K V} (hW₁ : PolarNondegOn Q W₁) (hperp : perp Q W₁ ≤ W₂)
    (h₁ : ∀ e ∈ W₁, ∀ w ∈ W₁, eichler Q e w ∈ H) (h₂ : ∀ e ∈ W₂, ∀ w ∈ W₂, eichler Q e w ∈ H)
    (P : HypPair Q) (hPe : P.e ∈ W₁ ⊓ W₂) (hPf : P.f ∈ W₁ ⊓ W₂) : elementaryGroup Q ≤ H := by
  have hroot : ∀ u ∈ W₁ ⊓ W₂, u ≠ 0 → Q u = 0 → IsRootCenter Q H u := by
    intro u hu hu0 hQu
    obtain ⟨hu₁, hu₂⟩ := Submodule.mem_inf.mp hu
    refine ⟨hu0, hQu, fun w hw => ?_⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hW₁).sup_eq_top ▸
      Submodule.mem_top (x := w))
    have hun : polar Q u n = 0 := mem_perp.mp hn u hu₁
    have huc : polar Q u c = 0 := by
      rw [polar_add_right, hun, add_zero] at hw
      exact hw
    rw [← eichler_mul huc hun]
    exact H.mul_mem (h₁ u hu₁ c hc) (h₂ u hu₂ n (hperp hn))
  exact elementaryGroup_le_of_hypPair hQ hH P (hroot _ hPe P.e_ne_zero P.Q_e)
    (hroot _ hPf P.f_ne_zero P.Q_f)

end Rel

section Normalize

variable {Y : Type*} [Group Y] {p : ℕ}

theorem map_hyperClosure_le_of_normalizes (φ : Y ≃* Y) {E : Subgroup Y}
    (hE : E.map φ.toMonoidHom = E) :
    (hyperClosure p ⊤ E).map φ.toMonoidHom ≤ hyperClosure p ⊤ E := by
  rw [hyperClosure, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, ⟨-, F, hFE, hF, hcomm⟩, rfl⟩
  refine ⟨Subgroup.mem_top _, F.map φ.toMonoidHom, hE ▸ Subgroup.map_mono hFE, ?_, ?_⟩
  · rw [← hE, Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact hF
  · rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hcomm f hf]

end Normalize

end CFSG.LieType.SeitzGeneration
