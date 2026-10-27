module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution

public section

namespace CFSG.ComponentClassification.SubgroupFixedInvolution

theorem two_group_normalizing {G : Type*} [Group G] [Finite G]
    (factor twoSubgroup : Subgroup G) (heven : Even (Nat.card factor))
    (htwo : IsPGroup 2 twoSubgroup)
    (hnormalizes : twoSubgroup ≤ Subgroup.normalizer (factor : Set G)) :
    ∃ member : G, member ∈ factor ∧ orderOf member = 2 ∧
      member ∈ Subgroup.centralizer (twoSubgroup : Set G) := by
  let action := factor.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)
  obtain ⟨member, horder, hfixed⟩ := TwoActionFixedInvolution.exists_fixed htwo heven action
  refine ⟨member.val, member.property, (orderOf_injective factor.subtype factor.subtype_injective member).trans horder, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro actor hactor
  have heq := congrArg Subtype.val (hfixed (⟨actor, hactor⟩ : twoSubgroup))
  change actor * member.val * actor⁻¹ = member.val at heq
  calc
    actor * member.val = (actor * member.val * actor⁻¹) * actor := by group
    _ = member.val * actor := by rw [heq]

theorem involution_normalizing {G : Type*} [Group G] [Finite G]
    (factor : Subgroup G) (heven : Even (Nat.card factor))
    (involution : G) (horder : orderOf involution = 2)
    (hnormalizes : involution ∈ Subgroup.normalizer (factor : Set G)) :
    ∃ member : G, member ∈ factor ∧ orderOf member = 2 ∧
      member ∈ Subgroup.centralizer {involution} := by
  have htwo : IsPGroup 2 (Subgroup.zpowers involution) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder, pow_one])
  obtain ⟨member, hmember, hmemberOrder, hcentralizes⟩ := two_group_normalizing factor
    (Subgroup.zpowers involution) heven htwo (Subgroup.zpowers_le.mpr hnormalizes)
  refine ⟨member, hmember, hmemberOrder, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp hcentralizes involution (Subgroup.mem_zpowers involution)).symm

end CFSG.ComponentClassification.SubgroupFixedInvolution
