module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem invariantTwoMaximalWithin_contains_normal_two_subgroup
    {G : Type*} [Group G] (actingGroup overgroup twoGroup normalGroup : Subgroup G)
    (hacting : actingGroup ≤ overgroup)
    (hmaximal : invariantTwoMaximalWithin actingGroup overgroup twoGroup)
    (hnormalContained : normalGroup ≤ overgroup)
    (hnormal : (normalGroup.subgroupOf overgroup).Normal)
    (hnormalGroup : IsPGroup 2 normalGroup) : normalGroup ≤ twoGroup := by
  have hnormalizer := (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalContained).mp hnormal
  have hjoinGroup := hmaximal.2.1.to_sup_of_normal_right' hnormalGroup
    (hmaximal.1.trans hnormalizer)
  have hjoinInvariant := (le_inf hmaximal.2.2.1 (hacting.trans hnormalizer)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup twoGroup normalGroup)
  have hequal := hmaximal.2.2.2 (twoGroup ⊔ normalGroup) (sup_le hmaximal.1 hnormalContained)
    hjoinGroup hjoinInvariant le_sup_left
  exact le_sup_right.trans hequal.le

theorem relative_maximal_pair_twoCore_eq_intersection_of_contained
    {G : Type*} [Group G] [Finite G]
    (actingGroup overgroup first second : Subgroup G)
    (_hacting : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstEscape : ¬ first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hintersection : first ⊓ overgroup = first ⊓ second)
    (hcoreContained : pCoreOf 2 (Subgroup.normalizer
      ((first ⊓ second : Subgroup G) : Set G)) ≤ overgroup)
    (hmaximal : ∀ largerFirst largerSecond : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
      ¬ largerFirst ≤ overgroup → largerSecond ≤ overgroup →
      Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G))
    (hglobalize : ∀ localSecond : Subgroup G,
      invariantTwoMaximalWithin actingGroup overgroup localSecond →
      rankTwoMaximalInvariantTwoSubgroup actingGroup localSecond) :
    pCoreOf 2 (Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G)) = first ⊓ second := by
  let intersection := first ⊓ second
  let localGroup := Subgroup.normalizer (intersection : Set G)
  let localCore := pCoreOf 2 localGroup
  have hlocalActor := common_normalizer_le_normalizer_inf actingGroup first second
    hfirst.2.1 hsecond.2.1
  have hintersectionCore : intersection ≤ localCore :=
    twoLocal_witness_le_pCoreOf intersection localGroup hfirst.1.to_inf_left rfl
  have hcoreInvariant : actingGroup ≤ Subgroup.normalizer (localCore : Set G) :=
    hlocalActor.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)
  have hnormalizingFirstInvariant := invariant_normalizer_intersection actingGroup first second
    hfirst.2.1 hsecond.2.1
  let extendedFirst := (first ⊓ localGroup) ⊔ localCore
  have hextendedGroup : IsPGroup 2 extendedFirst :=
    hfirst.1.to_inf_left.to_sup_of_normal_right' (pCoreOf_isPGroup 2 localGroup)
      (inf_le_right.trans (localGroup_le_normalizer_pCoreOf 2 localGroup))
  have hextendedInvariant : actingGroup ≤ Subgroup.normalizer (extendedFirst : Set G) :=
    (le_inf hnormalizingFirstInvariant hcoreInvariant).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (first ⊓ localGroup) localCore)
  obtain ⟨largerFirst, hextendedLe, hlargerFirst⟩ := exists_maximal_invariant_two_subgroup_containing
    actingGroup extendedFirst hextendedGroup hextendedInvariant
  have hlargerFirstEscape : ¬ largerFirst ≤ overgroup := by
    intro hbound
    have hfirstProper : intersection < first := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro hequal
      exact hfirstEscape (hequal.symm.le.trans (inf_le_right.trans hsecondLe))
    have hgrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
      first intersection hfirst.1 hfirstProper
    have hboundNormalizer : first ⊓ localGroup ≤ overgroup :=
      le_sup_left.trans (hextendedLe.trans hbound)
    have hboundIntersection : first ⊓ localGroup ≤ intersection :=
      (le_inf inf_le_left hboundNormalizer).trans hintersection.le
    exact hgrows.not_ge hboundIntersection
  obtain ⟨largerSecond, hcoreLeSecond, hwithin⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup overgroup localCore hcoreContained (pCoreOf_isPGroup 2 localGroup) hcoreInvariant
  have hcardBound := hmaximal largerFirst largerSecond hlargerFirst (hglobalize largerSecond hwithin)
    hlargerFirstEscape hwithin.1
  have hcoreLeBoth : localCore ≤ largerFirst ⊓ largerSecond :=
    le_inf (le_sup_right.trans hextendedLe) hcoreLeSecond
  have hcoreCardBound := (Subgroup.card_le_of_le hcoreLeBoth).trans hcardBound
  exact (Subgroup.eq_of_le_of_card_ge hintersectionCore hcoreCardBound).symm

end CFSG.RankThreeCoreUniqueness.Helpers
