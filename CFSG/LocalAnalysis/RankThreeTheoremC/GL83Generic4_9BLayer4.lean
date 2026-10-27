module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9BLayer3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

namespace Gen49BHyp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y}

theorem gen49bl_not_le (h : Gen49BHyp p S R Γ x) (hWC : KFactWeakClosure)
    (hR0 : CFSG.pCore p Y = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤) (hRK : R ≤ K) :
    False := by
  have hZ := h.gen49bl_center_eq_bot hR0 hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat : IsCatalogGroup K := h.catalog.simple_subgroup K hsimple hnonab
  obtain ⟨Q, hQ⟩ := h.gen49bl_exists_sylow
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  rw [hQ] at hP
  have hmem := gen49bl_mem_sylow_iff hP
  have hxK : x ∈ K := hRK h.mem
  have hR' : IsElemAbelian p (R.subgroupOf K) :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (h.gen49bl_commute (h.le_sylow a.2) (h.le_sylow b.2))),
      fun a ha => Subtype.ext (by rw [coe_pow, coe_one]; exact h.elemAbelian.2 _ ha)⟩
  have hR'c : Nat.card (R.subgroupOf K) = p ^ 2 := by
    rw [← h.card_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv
  have hR'P : R.subgroupOf K ≤ (P : Subgroup K) := fun u hu => (hmem u).mpr (h.le_sylow hu)
  have : IsSimpleGroup K := hsimple
  obtain ⟨g, hg1, hg2⟩ := hWC p Fact.out h.gen49bl_ne_two K ⊤ inferInstance
    (Subgroup.topEquiv.isSimpleGroup)
    (by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun hba => hab (congrArg Subtype.val hba)⟩)
    (IsCatalogGroup.of_mulEquiv Subgroup.topEquiv hcat)
    (by rw [coe_top, centralizer_univ, hZ])
    (by
      rw [card_top]
      exact (show p ∣ Nat.card R by rw [h.card_eq]; exact dvd_pow_self p two_ne_zero).trans
        (card_dvd_of_le hRK))
    P (top_sup_eq _)
    (IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (h.gen49bl_commute ((hmem a).mp a.2) ((hmem b).mp b.2))))
    (by
      rw [inf_top_eq]
      exact le_pRank_of_elemAbelian_card hR'P hR' hR'c)
    (zpowers ⟨x, hxK⟩) (zpowers_le.mpr ((hmem _).mpr (h.le_sylow h.mem)))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.gen49bl_orderOf_eq])
  apply hg2
  have hmapK : ∀ A : Subgroup K, (A.map K.subtype).map (MulAut.conj (g : Y)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map K.subtype := fun A => by
    rw [map_map, map_map]
    congr 1
  apply map_injective K.subtype_injective
  have h3 : (zpowers ⟨x, hxK⟩ : Subgroup K).map K.subtype = zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← hmapK, h3]
  refine h.weakClosed g ?_
  rw [← h3, hmapK]
  exact (map_mono hg1).trans (map_le_iff_le_comap.mpr fun k hk => (hmem k).mp hk)

theorem gen49bl_exists_mem_centralizer (h : Gen49BHyp p S R Γ x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hR0 : CFSG.pCore p Y = ⊥) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) : ∃ a ∈ R, a ≠ 1 ∧ a ∈ centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  have hZ := h.gen49bl_center_eq_bot hR0 hK
  refine h.gen49bl_not_le hWC hR0 hK fun r hr => ?_
  obtain ⟨g, ⟨hgS, hgK⟩, hg⟩ := h.gen49bl_exists_inner hInn hR0 hK (h.le_sylow hr)
  have hc : g⁻¹ * r ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 : r * k * r⁻¹ = g * k * g⁻¹ := hg k hk
    calc k * (g⁻¹ * r) = g⁻¹ * (g * k * g⁻¹) * r := by group
      _ = g⁻¹ * (r * k * r⁻¹) * r := by rw [h1]
      _ = (g⁻¹ * r) * k := by group
  have hcomm : g * (g⁻¹ * r) = (g⁻¹ * r) * g := mem_centralizer_iff.mp hc g hgK
  have h1 : g ^ p * (g⁻¹ * r) ^ p = 1 := by
    rw [← (show Commute g (g⁻¹ * r) from hcomm).mul_pow, mul_inv_cancel_left]
    exact h.elemAbelian.2 r hr
  have hgp : g ^ p = 1 := by
    have h2 : g ^ p ∈ centralizer (K : Set Y) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem hc p)
    have h3 : (⟨g ^ p, pow_mem hgK p⟩ : K) ∈ center K := mem_center_iff.mpr fun k =>
      Subtype.ext (mem_centralizer_iff.mp h2 k k.2)
    rw [hZ, mem_bot] at h3
    exact congrArg Subtype.val h3
  have hgR : g ∈ R := h.gen49bl_mem_of_pow_eq_one hgS hgp
  have hcR : g⁻¹ * r ∈ R := R.mul_mem (R.inv_mem hgR) hr
  by_cases hc1 : g⁻¹ * r = 1
  · exact (inv_mul_eq_one.mp hc1) ▸ hgK
  · exact absurd hc (hall _ hcR hc1)

theorem gen49bl_le_centralizer (h : Gen49BHyp p S R Γ x) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hR0 : CFSG.pCore p Y = ⊥) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hKΓ : ¬ K ≤ Γ) : K ≤ centralizer ({x} : Set Y) := by
  obtain ⟨a, haR, ha1, haC⟩ := h.gen49bl_exists_mem_centralizer hInn hWC hR0 hK
  by_cases hax : zpowers a = zpowers x
  · have hxC : x ∈ centralizer (K : Set Y) :=
      (zpowers_le.mpr haC) (hax ▸ mem_zpowers x)
    intro k hk
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hxC k hk
  · exfalso
    apply hKΓ
    intro k hk
    apply (h.others a haR ha1 hax).1
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp haC k hk

theorem gen49bl_mem_of_not_le (h : Gen49BHyp p S R Γ x) {K K' : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) (hne : K ≠ K') (hKΓ : ¬ K ≤ Γ) :
    x ∈ K' := by
  obtain ⟨Q, hQ⟩ := h.gen49bl_exists_sylow
  obtain ⟨t, ⟨htS, htK'⟩, hto, -⟩ :=
    exists_mem_sylow_inf_component Fact.out h.gen49bl_ne_two h.core_eq_bot Q hK'
  rw [hQ] at htS
  have htR : t ∈ R := h.gen49bl_mem_of_pow_eq_one htS (hto ▸ pow_orderOf_eq_one t)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hto
    exact (Fact.out : p.Prime).one_lt.ne hto
  by_cases htx : zpowers t = zpowers x
  · exact zpowers_le.mpr htK' (htx ▸ mem_zpowers x)
  · exfalso
    apply hKΓ
    intro k hk
    apply (h.others t htR ht1 htx).1
    have hc : K' ≤ centralizer (K : Set Y) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK hne.symm)
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (hc htK') k hk

theorem gen49bl_eq_of_not_le (h : Gen49BHyp p S R Γ x) (hR0 : CFSG.pCore p Y = ⊥)
    {K K' : Subgroup Y} (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) (hKΓ : ¬ K ≤ Γ)
    (hK'Γ : ¬ K' ≤ Γ) : K = K' := by
  by_contra hne
  have hx : x ∈ K ⊓ K' := ⟨h.gen49bl_mem_of_not_le hK' hK (Ne.symm hne) hK'Γ,
    h.gen49bl_mem_of_not_le hK hK' hne hKΓ⟩
  rw [h.gen49bl_inf_eq_bot hR0 hK hK' hne, mem_bot] at hx
  exact h.ne_one hx

end Gen49BHyp

end CFSG.LocalAnalysis.RankThreeTheoremC
