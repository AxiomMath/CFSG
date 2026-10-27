module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

namespace ZLayerData3

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X}

omit [Finite X] in
private theorem le_layer {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    K ≤ rankThreeLayer (⊤ : Subgroup X) :=
  le_sSup hK

theorem le_core_of_center_eq_bot (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K = ⊥) :
    K ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  obtain ⟨K₁, hK₁, hZ₁⟩ := h.exists_component_center_ne_bot
  have hne : K₁ ≠ K := by
    rintro rfl
    exact hZ₁ hZ
  obtain ⟨hzK₁, hzc₁, -⟩ := h.component_center hK₁ hZ₁
  obtain ⟨a, haP, ha3, haz⟩ := h.exists_inf_ne_of_center_ne_bot hK₁ hZ₁
  obtain ⟨t, htP, ht3⟩ := h.exists_inf_of_center_eq_bot hK hZ
  have haK₁ : a ∈ K₁ := haP.2
  have htK : t ∈ K := htP.2
  refine le_rankThreeAschCore_of_commuting_triple h.memP haP.1 htP.1 h.ord ha3 ht3
    (hzc₁ a haK₁) (h.commute_layer (le_layer hK htK))
    (commute_of_isComponentOf_ne hK₁ hK hne a haK₁ t htK) haz ?_
    (fun k hk => h.commute_layer (le_layer hK hk))
    (fun k hk => commute_of_isComponentOf_ne hK₁ hK hne a haK₁ k hk)
  intro htza
  have htK₁ : t ∈ K₁ := sup_le (zpowers_le.2 hzK₁) (zpowers_le.2 haK₁) htza
  have hcen : (⟨t, htK⟩ : K) ∈ center K :=
    mem_center_iff.2 fun k =>
      Subtype.ext (commute_of_isComponentOf_ne hK₁ hK hne t htK₁ k k.2).symm
  rw [hZ, mem_bot] at hcen
  have ht1 : t = 1 := congrArg Subtype.val hcen
  rw [ht1, orderOf_one] at ht3
  omega

theorem le_core_of_centralizing_element (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) {c : X} (hcP : c ∈ (P : Subgroup X))
    (hcK : ∀ k ∈ K, c * k = k * c) (hc3 : orderOf c = 3) (hcz : c ∉ zpowers z) :
    K ≤ rankThreeAschCore 2 3 (P : Subgroup X) := by
  obtain ⟨hzK, hzcK, hω⟩ := h.component_center hK hZ
  obtain ⟨d, hdP, hd3, hdz⟩ := h.exists_inf_ne_of_center_ne_bot hK hZ
  have hzc : z * c = c * z := (mem_centralizer_iff.1 h.cent c hcP).symm
  refine le_rankThreeAschCore_of_commuting_triple h.memP hcP hdP.1 h.ord hc3 hd3 hzc
    (hzcK d hdP.2) (hcK d hdP.2) hcz ?_ hzcK hcK
  intro hd
  have hcomm : ∀ x ∈ zpowers z, ∀ y ∈ zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (show Commute z c from hzc) m n).eq
  obtain ⟨u, hu, v, hv, huv⟩ := exists_eq_mul_of_mem_sup_of_commute hcomm hd
  have hvK : v ∈ K := by
    have := K.mul_mem (K.inv_mem (zpowers_le.2 hzK hu)) hdP.2
    rwa [huv, inv_mul_cancel_left] at this
  have hvc : ∀ k ∈ K, v * k = k * v := by
    intro k hk
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hv
    exact (Commute.zpow_left (show Commute c k from hcK k hk) n).eq
  by_cases hv1 : v = 1
  · rw [huv, hv1, mul_one] at hdz
    exact hdz hu
  · have hv3 : orderOf v = 3 := by
      have hdvd : orderOf v ∣ 3 := hc3 ▸ orderOf_dvd_of_mem_zpowers hv
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.1 h1) hv1
      · exact h3
    have hcv : zpowers v = zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hv) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hv3, hc3]
    exact hcz (zpowers_le.2 (hω v hvK hvc hv3) (hcv ▸ mem_zpowers c))

theorem normalizes_of_not_le_core (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥)
    (hnot : ¬ K ≤ rankThreeAschCore 2 3 (P : Subgroup X)) :
    (P : Subgroup X) ≤ normalizer (K : Set X) := by
  intro g hg
  by_contra hgn
  have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := fun he =>
    hgn (mem_normalizer_iff_map_conj_eq.2 he)
  obtain ⟨d, hdP, hd3, hdz⟩ := h.exists_inf_ne_of_center_ne_bot hK hZ
  refine hnot (h.le_core_of_centralizing_element hK hZ (c := g * d * g⁻¹)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hdP.1) (Subgroup.inv_mem _ hg)) ?_ ?_ ?_)
  · intro k hk
    exact commute_of_isComponentOf_ne (isComponentOf_map_conj hK g) hK hne _
      ⟨d, hdP.2, rfl⟩ k hk
  · exact (MulEquiv.orderOf_eq (MulAut.conj g) d).trans hd3
  · intro hw
    have hgw : g * (g * d * g⁻¹) = g * d * g⁻¹ * g :=
      mem_centralizer_iff.1 (zpowers_le.2 h.cent hw) g hg
    refine hdz ?_
    have hdw : d = g * d * g⁻¹ :=
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹ * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * (g * d * g⁻¹)) := by rw [hgw]
        _ = g * d * g⁻¹ := inv_mul_cancel_left g _
    rw [hdw]
    exact hw

theorem omega_of_not_le_core (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥)
    (hnot : ¬ K ≤ rankThreeAschCore 2 3 (P : Subgroup X)) :
    ∀ c ∈ (P : Subgroup X) ⊓ centralizer (K : Set X), orderOf c = 3 → c ∈ zpowers z := by
  intro c hc hc3
  by_contra hcz
  exact hnot (h.le_core_of_centralizing_element hK hZ hc.1
    (fun k hk => (mem_centralizer_iff.1 hc.2 k hk).symm) hc3 hcz)

end ZLayerData3

end CFSG.LocalAnalysis.RankThreeTheoremC
