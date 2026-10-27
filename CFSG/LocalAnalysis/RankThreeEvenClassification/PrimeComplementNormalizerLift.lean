module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalPrimeSupplement

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem prime_complement_normal_image_normalizer_sup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (normal subgroup : Subgroup G) [normal.Normal]
    (hcomplement : ¬prime ∣ Nat.card normal) (hpgroup : IsPGroup prime subgroup)
    (himageNormal : (subgroup.map (QuotientGroup.mk' normal)).Normal) :
    normal ⊔ Subgroup.normalizer (subgroup : Set G) = ⊤ := by
  have : Fact prime.Prime := ⟨hprime⟩
  let quotient := QuotientGroup.mk' normal
  let overgroup := (subgroup.map quotient).comap quotient
  have : (subgroup.map quotient).Normal := himageNormal
  have : overgroup.Normal := inferInstance
  have hovergroup : overgroup = subgroup ⊔ normal := by
    change (subgroup.map quotient).comap quotient = subgroup ⊔ normal
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hsubgroupLe : subgroup ≤ overgroup := hovergroup.symm ▸ le_sup_left
  have hnormalLe : normal ≤ overgroup := hovergroup.symm ▸ le_sup_right
  let internalSubgroup := subgroup.subgroupOf overgroup
  let internalNormal := normal.subgroupOf overgroup
  have hsup : internalNormal ⊔ internalSubgroup = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hnormalLe hsubgroupLe, sup_comm, ← hovergroup, Subgroup.subgroupOf_self]
  have hnormalComplement : ¬prime ∣ Nat.card internalNormal := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnormalLe).toEquiv]
    exact hcomplement
  have hindexComplement : ¬prime ∣ internalSubgroup.index := fun hdivides =>
    hnormalComplement (hdivides.trans (index_dvd_normal_supplement_card internalNormal internalSubgroup hsup))
  have hinternalGroup : IsPGroup prime internalSubgroup :=
    hpgroup.comap_of_injective overgroup.subtype overgroup.subtype_injective
  let sylow := hinternalGroup.toSylow hindexComplement
  have hfrattini := Sylow.normalizer_sup_eq_top (N := overgroup) sylow
  have hsylowMap : (sylow : Subgroup overgroup).map overgroup.subtype = subgroup := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subgroupOf_eq_of_le hsubgroupLe
  rw [hsylowMap] at hfrattini
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact le_sup_right
  · rw [hovergroup]
    exact sup_le (Subgroup.le_normalizer.trans le_sup_right) le_sup_left

theorem prime_complement_normal_image_normalizer_product {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (normal subgroup : Subgroup G) [normal.Normal]
    (hcomplement : ¬prime ∣ Nat.card normal) (hpgroup : IsPGroup prime subgroup)
    (himageNormal : (subgroup.map (QuotientGroup.mk' normal)).Normal) :
    ∀ member : G, ∃ first ∈ normal, ∃ second ∈ Subgroup.normalizer (subgroup : Set G),
      first * second = member := by
  have hsup := prime_complement_normal_image_normalizer_sup prime hprime normal subgroup
    hcomplement hpgroup himageNormal
  intro member
  apply Subgroup.mem_sup_of_normal_left.mp
  rw [hsup]
  exact Subgroup.mem_top member

end CFSG.RankThreeEvenClassification.Helpers
