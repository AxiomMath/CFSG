module

public import CFSG.GH74.Uniqueness.SU.KI6BCase1

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem Cfg.oddCore_eq_bot (h : Cfg H T H₀) :
    CFSG.Open.componentClassificationOddCore H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply sSup_eq_bot.mpr
  intro N hN
  have : N ≤ pPrimeCore 2 H :=
    le_sSup (show N ∈ {K : Subgroup H | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩)
  rw [h.odd] at this
  exact le_bot_iff.mp this

theorem Cfg.layer_eq_sup_of_two (h : Cfg H T H₀) {K₁ K₂ : Subgroup H} (hK₁ : IsComponent K₁)
    (hK₂ : IsComponent K₂) (hne : K₂ ≠ K₁) : layer H = K₁ ⊔ K₂ := by
  have hbound := (proper_full_core_component_number_restrictions T H₀ h.ne h.sylow_le
    h.gamma).2.2.2 h.oddCore_eq_bot
  have hsub : ({K₁, K₂} : Set (Subgroup H)) ⊆ {L : Subgroup H | Open.IsComponentOf L ⊤} := by
    intro L hL
    rcases hL with rfl | rfl
    · exact isComponentOf_top_of_isComponent hK₁
    · exact isComponentOf_top_of_isComponent hK₂
  have hcard : ({K₁, K₂} : Set (Subgroup H)).ncard = 2 := Set.ncard_pair hne.symm
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hbound.2) (Set.toFinite _)
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    have : L ∈ ({K₁, K₂} : Set (Subgroup H)) := by
      rw [heq]; exact isComponentOf_top_of_isComponent hL
    rcases this with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (component_le_layer hK₁) (component_le_layer hK₂)


theorem Cfg.generalizedFitting_eq_sup_of_two (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K₁ K₂ : Subgroup H} (hK₁ : IsComponent K₁) (hK₁H : ¬ K₁ ≤ H₀)
    (hK₂ : IsComponent K₂) (hne : K₂ ≠ K₁) : generalizedFitting H = K₁ ⊔ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlayer := h.layer_eq_sup_of_two hK₁ hK₂ hne
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  have hP1 := h.pRank_centralizer_eq_one F hr htc ht2 hK₁ hK₁H
  have hdata := component_data F h htc ht2 hK₂ (hr K₂ hK₂)
  obtain ⟨y, hyK, hy4⟩ := hdata.2.2.2
  have hQK : pCore 2 H ≤ K₂ := by
    intro w hw
    by_contra hwK
    have hcomm : y * w = w * y := (h.pCore_comm_layer hw (component_le_layer hK₂ hyK)).symm
    have htK : t ∈ K₂ := hdata.1
    have hrank := two_le_pRank_of_order_four F h htc ht2 hK₂ (hr K₂ hK₂) hyK hy4 hcomm
      (fun hmem => hwK (Subgroup.zpowers_le.mpr htK hmem))
      (by
        obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨w, hw⟩
        exact ⟨n, congrArg Subtype.val hn⟩)
      (fun g hg1 hg2 => h.pCore_inf_component_le F htc ht2 hK₂ (hr K₂ hK₂)
        ((Subgroup.zpowers_le.mpr hw) hg2) (Subgroup.zpowers_le.mpr hyK hg1))
    have hyC : y ∈ centralizer (K₁ : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact components_commute hK₁ hK₂ hne.symm k hk y hyK
    have hwC : w ∈ centralizer (K₁ : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (h.pCore_comm_layer hw (component_le_layer hK₁ hk)).symm
    have hle : zpowers y ⊔ zpowers w ≤ centralizer (K₁ : Set H) :=
      sup_le (Subgroup.zpowers_le.mpr hyC) (Subgroup.zpowers_le.mpr hwC)
    have := (hrank.trans (SU1.pRank_mono (by norm_num) hle)).trans hP1.le
    omega
  apply le_antisymm
  · refine sup_le ?_ (hlayer.le)
    rw [hfit]
    exact hQK.trans le_sup_right
  · rw [← hlayer]; exact le_sup_right

theorem Cfg.mem_generalizedFitting_of_involution (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K₁ K₂ : Subgroup H} (hK₁ : IsComponent K₁) (hK₁H : ¬ K₁ ≤ H₀)
    (hK₂ : IsComponent K₂) (hK₂H : ¬ K₂ ≤ H₀) (hne : K₂ ≠ K₁)
    (hFeq : generalizedFitting H = K₁ ⊔ K₂) {u : H} (huT : u ∈ (T : Subgroup H))
    (hu2 : u * u = 1) : u ∈ generalizedFitting H := by
  obtain ⟨k₁, hk₁, hc₁⟩ := h.exists_inner F hr htc ht2 hK₁ hK₁H huT hu2
  obtain ⟨k₂, hk₂, hc₂⟩ := h.exists_inner F hr htc ht2 hK₂ hK₂H huT hu2
  have hcomm12 : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb =>
    (components_commute hK₁ hK₂ hne.symm b hb a ha).symm
  have hK₂C : K₂ ≤ centralizer (K₁ : Set H) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact components_commute hK₁ hK₂ hne.symm k hk x hx
  have hK₁C : K₁ ≤ centralizer (K₂ : Set H) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (components_commute hK₁ hK₂ hne.symm x hx k hk).symm
  set w : H := u * k₁⁻¹ * k₂⁻¹ with hw
  have hw1 : w ∈ centralizer (K₁ : Set H) :=
    Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ (hK₂C hk₂))
  have hw2 : w ∈ centralizer (K₂ : Set H) := by
    have : w = (u * k₂⁻¹) * k₁⁻¹ := by
      have hcomm : k₁⁻¹ * k₂⁻¹ = k₂⁻¹ * k₁⁻¹ := by
        have := hcomm12 k₂⁻¹ (K₂.inv_mem hk₂) k₁⁻¹ (K₁.inv_mem hk₁)
        exact this.symm
      calc w = u * (k₁⁻¹ * k₂⁻¹) := by rw [hw]; group
        _ = u * (k₂⁻¹ * k₁⁻¹) := by rw [hcomm]
        _ = (u * k₂⁻¹) * k₁⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hc₂ (Subgroup.inv_mem _ (hK₁C hk₁))
  have hwF : w ∈ generalizedFitting H := by
    apply centralizer_generalizedFitting_le H
    rw [hFeq]
    have h1 : zpowers w ≤ centralizer (K₁ : Set H) := Subgroup.zpowers_le.mpr hw1
    have h2 : zpowers w ≤ centralizer (K₂ : Set H) := Subgroup.zpowers_le.mpr hw2
    have h3 : K₁ ⊔ K₂ ≤ centralizer ((zpowers w : Subgroup H) : Set H) :=
      sup_le (Subgroup.le_centralizer_iff.mpr h1) (Subgroup.le_centralizer_iff.mpr h2)
    have h4 : zpowers w ≤ centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) :=
      Subgroup.le_centralizer_iff.mpr h3
    exact h4 (Subgroup.mem_zpowers w)
  have hk₁F : k₁ ∈ generalizedFitting H := by rw [hFeq]; exact Subgroup.mem_sup_left hk₁
  have hk₂F : k₂ ∈ generalizedFitting H := by rw [hFeq]; exact Subgroup.mem_sup_right hk₂
  have : u = w * k₂ * k₁ := by rw [hw]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwF hk₂F) hk₁F


theorem ki6B_of_facts (F : KI6BFacts) : KI6B := by
  intro H _ _ T H₀ h hr
  obtain ⟨t, htc, ht2⟩ := exists_central_involution h.odd h.cen
  have hFH := h.generalizedFitting_sup_eq_top F hr htc ht2
  obtain ⟨K₁, hK₁, hK₁H⟩ := h.exists_component_not_le F hr htc ht2
  have hP1 := h.pRank_centralizer_eq_one F hr htc ht2 hK₁ hK₁H
  have hcyc := h.isCyclic_center F hr htc ht2 hK₁ hK₁H
  have hsl := (component_sl25 F h hr htc ht2 hK₁ hK₁H).2
  by_cases huniq : ∀ K₂ : Subgroup H, IsComponent K₂ → ¬ K₂ ≤ H₀ → K₂ = K₁
  · refine ⟨K₁, hK₁, hK₁H, hP1, Or.inl ⟨?_, Or.inl hsl, ?_, h.closure_le F hr htc ht2 hK₁ hK₁H⟩,
      Or.inr hcyc⟩
    · exact h.normal_of_unique hFH hK₁ hK₁H huniq
    · exact h.centralizer_component_le F hr htc ht2 hK₁ hK₁H huniq
  · push Not at huniq
    obtain ⟨K₂, hK₂, hK₂H, hne⟩ := huniq
    have hFeq := h.generalizedFitting_eq_sup_of_two F hr htc ht2 hK₁ hK₁H hK₂ hne
    refine ⟨K₁, hK₁, hK₁H, hP1, Or.inr (Or.inl ⟨hsl, K₂, hK₂, hne,
      (component_sl25 F h hr htc ht2 hK₂ hK₂H).2, hFeq, ?_⟩), Or.inr hcyc⟩
    rw [Subgroup.closure_le]
    rintro g ⟨hgT, hg2⟩
    exact h.mem_generalizedFitting_of_involution F hr htc ht2 hK₁ hK₁H hK₂ hK₂H hne hFeq hgT hg2

end CFSG.GH74.Uniqueness.SU.K.R6
