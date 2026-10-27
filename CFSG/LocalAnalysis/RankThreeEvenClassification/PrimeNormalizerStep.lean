module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem pGroup_exists_prime_normalizer_step {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (subgroup : Subgroup G) (hproper : subgroup ≠ ⊤) :
    ∃ element : G, element ∈ Subgroup.normalizer (subgroup : Set G) ∧ element ∉ subgroup ∧
      (subgroup.subgroupOf (subgroup ⊔ Subgroup.zpowers element)).Normal ∧
        subgroup.relIndex (subgroup ⊔ Subgroup.zpowers element) = prime := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent G := hpgroup.isNilpotent
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let kernel := subgroup.subgroupOf normalizer
  have : kernel.Normal := Subgroup.normal_in_normalizer
  have hkernelProper : kernel ≠ ⊤ := by
    intro heq
    have hle : normalizer ≤ subgroup := Subgroup.subgroupOf_eq_top.mp heq
    have hstrict := Group.normalizerCondition_of_isNilpotent subgroup (lt_top_iff_ne_top.mpr hproper)
    exact hstrict.not_ge hle
  have hquotientPGroup : IsPGroup prime (normalizer ⧸ kernel) :=
    (hpgroup.to_subgroup normalizer).of_surjective (QuotientGroup.mk' kernel)
      (QuotientGroup.mk'_surjective kernel)
  have hdivisor : prime ∣ Nat.card (normalizer ⧸ kernel) := by
    rcases hquotientPGroup.card_eq_or_dvd with hcard | hdivisor
    · have hindex : kernel.index = 1 := by rwa [Subgroup.index_eq_card]
      exact False.elim (hkernelProper (Subgroup.index_eq_one.mp hindex))
    · exact hdivisor
  obtain ⟨quotientElement, horder⟩ := exists_prime_orderOf_dvd_card' prime hdivisor
  obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective kernel quotientElement
  have hnot : (element : G) ∉ subgroup := by
    intro hmem
    have hkernel : element ∈ (QuotientGroup.mk' kernel).ker := by
      rw [QuotientGroup.ker_mk']
      exact hmem
    have hone : quotientElement = 1 := helement.symm.trans (MonoidHom.mem_ker.mp hkernel)
    rw [hone, orderOf_one] at horder
    exact hprime.ne_one horder.symm
  have hnormalized : subgroup ⊔ Subgroup.zpowers (element : G) ≤ normalizer :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le_of_mem element.property)
  have hnormal : (subgroup.subgroupOf (subgroup ⊔ Subgroup.zpowers (element : G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnormalized
  refine ⟨element, element.property, hnot, hnormal, ?_⟩
  have hrel : kernel.relIndex (Subgroup.zpowers element) = prime := by
    rw [← QuotientGroup.ker_mk' kernel, Subgroup.relIndex_ker, MonoidHom.map_zpowers,
      helement, Nat.card_zpowers, horder]
  have hsup : kernel.relIndex (kernel ⊔ Subgroup.zpowers element) = kernel.relIndex (Subgroup.zpowers element) :=
    Subgroup.relIndex_sup_left (Subgroup.zpowers element) kernel
  have hmap : (kernel ⊔ Subgroup.zpowers element).map normalizer.subtype =
      subgroup ⊔ Subgroup.zpowers (element : G) := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, MonoidHom.map_zpowers]
    rfl
  have hrelSup := Subgroup.relIndex_map_map normalizer.subtype kernel (kernel ⊔ Subgroup.zpowers element)
  rw [Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, hmap,
    normalizer.subtype.ker_eq_bot normalizer.subtype_injective, sup_bot_eq, sup_bot_eq] at hrelSup
  exact hrelSup.trans (hsup.trans hrel)

theorem pGroup_exists_prime_normalizer_step_between {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (overgroup subgroup : Subgroup G)
    (hpgroup : IsPGroup prime overgroup) (hproper : subgroup < overgroup) :
    ∃ element ∈ overgroup, element ∈ Subgroup.normalizer (subgroup : Set G) ∧ element ∉ subgroup ∧
      (subgroup.subgroupOf (subgroup ⊔ Subgroup.zpowers element)).Normal ∧
        subgroup.relIndex (subgroup ⊔ Subgroup.zpowers element) = prime := by
  have hrestricted : subgroup.subgroupOf overgroup ≠ ⊤ := by
    intro heq
    exact hproper.not_ge (Subgroup.subgroupOf_eq_top.mp heq)
  obtain ⟨element, hnormalized, hnot, _, hindex⟩ := pGroup_exists_prime_normalizer_step prime hprime hpgroup
    (subgroup.subgroupOf overgroup) hrestricted
  have hambientNormalizer : (element : G) ∈ Subgroup.normalizer (subgroup : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro member
    constructor
    · intro hmember
      have hconjugate := (Subgroup.mem_normalizer_iff.mp hnormalized
        (⟨member, hproper.le hmember⟩ : overgroup)).mp hmember
      exact hconjugate
    · intro hconjugate
      have hmemberOvergroup : member ∈ overgroup := by
        have heq : member = (element : G)⁻¹ * ((element : G) * member * (element : G)⁻¹) * element := by group
        rw [heq]
        exact overgroup.mul_mem (overgroup.mul_mem (overgroup.inv_mem element.property)
          (hproper.le hconjugate)) element.property
      exact (Subgroup.mem_normalizer_iff.mp hnormalized (⟨member, hmemberOvergroup⟩ : overgroup)).mpr hconjugate
  refine ⟨element, element.property, hambientNormalizer, hnot, ?_, ?_⟩
  · apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le_of_mem hambientNormalizer)
  · have hmap : ((subgroup.subgroupOf overgroup) ⊔ Subgroup.zpowers element).map overgroup.subtype =
        subgroup ⊔ Subgroup.zpowers (element : G) := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hproper.le, MonoidHom.map_zpowers]
      rfl
    have htransport := Subgroup.relIndex_map_map overgroup.subtype (subgroup.subgroupOf overgroup)
      ((subgroup.subgroupOf overgroup) ⊔ Subgroup.zpowers element)
    rw [Subgroup.map_subgroupOf_eq_of_le hproper.le, hmap,
      overgroup.subtype.ker_eq_bot overgroup.subtype_injective, sup_bot_eq, sup_bot_eq] at htransport
    exact htransport.trans hindex

end CFSG.RankThreeEvenClassification.Helpers
