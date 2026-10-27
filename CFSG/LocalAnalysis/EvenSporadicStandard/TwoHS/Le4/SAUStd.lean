module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUType
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUOrb

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

theorem exists_conf_at (H : Sect7Hyps G L f s y S₀ n) {r0 : G} {Θ0 : HModel →* G}
    (hc0 : FyConf (f ^ 2) r0 Θ0) (hs0 : FyCoset L f y Θ0) {r : G} (hr : r * f ^ 2 = f ^ 2 * r)
    (hr3 : orderOf r = 3) :
    ∃ m : G, m * f ^ 2 = f ^ 2 * m ∧ FyConf (f ^ 2) r (confConj m⁻¹ Θ0) ∧
      FyCoset L f y (confConj m⁻¹ Θ0) := by
  obtain ⟨m, hm_t, hm⟩ := hc0.one_class r hr hr3
  have hmt' : m⁻¹ * f ^ 2 = f ^ 2 * m⁻¹ := by
    calc m⁻¹ * f ^ 2 = m⁻¹ * f ^ 2 * m * m⁻¹ := by group
      _ = m⁻¹ * (f ^ 2 * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * f ^ 2) * m⁻¹ := by rw [hm_t]
      _ = f ^ 2 * m⁻¹ := by group
  have hmr : m⁻¹ * r0 * m⁻¹⁻¹ = r := by
    calc m⁻¹ * r0 * m⁻¹⁻¹ = m⁻¹ * (m * r * m⁻¹) * m := by rw [hm]; group
      _ = r := by group
  refine ⟨m, hm_t, ?_, hs0.conj m⁻¹ (H.normalizes_f hmt') (H.normalizes_y hmt')⟩
  have := hc0.conj m⁻¹ hmt'
  rwa [hmr] at this

theorem SAU.IsW.not_mem_LF (H : Sect7Hyps G L f s y S₀ n) (h : Sect8Hyp C f n S₀) {u : G}
    (hu : SAU.IsW C f L y u) : u ∉ L ⊔ zpowers f := by
  intro hmem
  obtain ⟨l, hl, i, hu'⟩ := exists_mul_zpow_of_mem_sup (SAU.hcom H) hmem
  have hcu : u * f = f * u := by
    rw [hu']
    exact ((show Commute l f from SAU.hcom H l hl).mul_left
      (Commute.zpow_left (Commute.refl f) i)).eq
  have h1 := hu.2.1 f h.f_mem
  rw [hcu] at h1
  have h2 : f = f⁻¹ := by
    calc f = f * u * u⁻¹ := by group
      _ = f⁻¹ := h1
  have h3 : f ^ 2 = 1 := by
    calc f ^ 2 = f * f := sq f
      _ = f * f⁻¹ := by rw [← h2]
      _ = 1 := by group
  have := orderOf_dvd_of_pow_eq_one h3
  rw [H.four.order] at this
  omega

section Std

variable {r0 : G} {Θ0 : HModel →* G}

theorem std_of_three (H : Sect7Hyps G L f s y S₀ n) (hc0 : FyConf (f ^ 2) r0 Θ0)
    (hs0 : FyCoset L f y Θ0) {r u ρ : G} (hr : r * f ^ 2 = f ^ 2 * r) (hr3 : orderOf r = 3)
    (hut : u * f ^ 2 = f ^ 2 * u) (hur : u * r = r * u) (huu : u * u = 1)
    (hnf : u ∉ L ⊔ zpowers f) (hy : u ∈ L ⊔ zpowers y) (hρ3 : ρ ^ 3 = 1)
    (hρt : ρ * f ^ 2 = f ^ 2 * ρ) (hρr : ρ * r = r * ρ) (hρn : ρ ∉ zpowers r)
    (hρu : ρ * u = u * ρ) :
    ∃ c : G, c * f ^ 2 = f ^ 2 * c ∧ u = c * Θ0 (DihedralGroup.sr 0, 1, 1) * c⁻¹ := by
  obtain ⟨m, hm_t, hconf, hcos⟩ := exists_conf_at H hc0 hs0 hr hr3
  obtain ⟨k, σ, hu, hσ2, hpar⟩ := hconf.ly_coords hcos hut hur huu hnf hy
  have hsig := hconf.sig_of_three hu hσ2 hρ3 hρt hρr hρn hρu
  obtain ⟨nn, hnn, hcl⟩ := hconf.ly_class hσ2 hpar hsig
  have hmt' : m⁻¹ * f ^ 2 = f ^ 2 * m⁻¹ := by
    calc m⁻¹ * f ^ 2 = m⁻¹ * f ^ 2 * m * m⁻¹ := by group
      _ = m⁻¹ * (f ^ 2 * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * f ^ 2) * m⁻¹ := by rw [hm_t]
      _ = f ^ 2 * m⁻¹ := by group
  refine ⟨nn * m⁻¹, ?_, ?_⟩
  · calc nn * m⁻¹ * f ^ 2 = nn * (m⁻¹ * f ^ 2) := by group
      _ = nn * (f ^ 2 * m⁻¹) := by rw [hmt']
      _ = (nn * f ^ 2) * m⁻¹ := by group
      _ = (f ^ 2 * nn) * m⁻¹ := by rw [hnn]
      _ = f ^ 2 * (nn * m⁻¹) := by group
  · rw [hu, hcl, confConj_apply]
    group

end Std

end CFSG.EvenSporadicStandard.TwoHS
