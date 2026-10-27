module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem conjugate_subgroup_le_iff_of_conjugator_mem
    {G : Type*} [Group G] (subgroup overgroup : Subgroup G)
    (conjugator : G) (hconjugator : conjugator ∈ overgroup) :
    Subgroup.map (MulAut.conj conjugator).toMonoidHom subgroup ≤ overgroup ↔
      subgroup ≤ overgroup := by
  constructor
  · intro hmap element helement
    have hconjugate := hmap (Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom helement)
    change conjugator * element * conjugator⁻¹ ∈ overgroup at hconjugate
    have hresult := overgroup.mul_mem
      (overgroup.mul_mem (overgroup.inv_mem hconjugator) hconjugate) hconjugator
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hresult
  · intro hbound
    rintro element ⟨preimage, hpreimage, rfl⟩
    exact overgroup.mul_mem (overgroup.mul_mem hconjugator (hbound hpreimage))
      (overgroup.inv_mem hconjugator)

theorem invariantTwoMaximalWithin_global_of_normalizer_le
    {G : Type*} [Group G] [Finite G] (actingGroup overgroup twoGroup : Subgroup G)
    (hacting : actingGroup ≤ overgroup)
    (hmaximal : invariantTwoMaximalWithin actingGroup overgroup twoGroup)
    (hnormalizer : Subgroup.normalizer (twoGroup : Set G) ≤ overgroup) :
    rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup := by
  refine ⟨hmaximal.2.1, hmaximal.2.2.1, ?_⟩
  intro larger hgroup hinvariant hcontains
  have hintersectionInvariant := common_normalizer_le_normalizer_inf actingGroup larger overgroup
    hinvariant (hacting.trans Subgroup.le_normalizer)
  have hintersection := hmaximal.2.2.2 (larger ⊓ overgroup) inf_le_right hgroup.to_inf_left
    hintersectionInvariant (le_inf hcontains hmaximal.1)
  by_contra hdistinct
  have hproper : twoGroup < larger := lt_of_le_of_ne hcontains (fun hequal => hdistinct hequal.symm)
  have hgrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    larger twoGroup hgroup hproper
  have hbound : larger ⊓ Subgroup.normalizer (twoGroup : Set G) ≤ twoGroup := by
    exact (inf_le_inf_left larger hnormalizer).trans hintersection.le
  exact hgrows.not_ge hbound

theorem relative_maximal_pair_intersection_eq_overgroup_intersection
    {G : Type*} [Group G] [Finite G]
    (actingGroup overgroup first second : Subgroup G)
    (hacting : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (_hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstEscape : ¬ first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hmaximal : ∀ largerFirst largerSecond : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
      ¬ largerFirst ≤ overgroup → largerSecond ≤ overgroup →
      Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G))
    (hglobalize : ∀ localSecond : Subgroup G,
      invariantTwoMaximalWithin actingGroup overgroup localSecond →
      rankTwoMaximalInvariantTwoSubgroup actingGroup localSecond) :
    first ⊓ overgroup = first ⊓ second := by
  have hinvariant := common_normalizer_le_normalizer_inf actingGroup first overgroup
    hfirst.2.1 (hacting.trans Subgroup.le_normalizer)
  obtain ⟨largerSecond, hcommonLe, hwithin⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup overgroup (first ⊓ overgroup) inf_le_right hfirst.1.to_inf_left hinvariant
  have hbound := hmaximal first largerSecond hfirst (hglobalize largerSecond hwithin)
    hfirstEscape hwithin.1
  have hcard := Subgroup.card_le_of_le
    (le_inf inf_le_left hcommonLe : first ⊓ overgroup ≤ first ⊓ largerSecond)
  exact (Subgroup.eq_of_le_of_card_ge (inf_le_inf_left first hsecondLe)
    (hcard.trans hbound)).symm

theorem exists_relative_maximal_invariant_pair
    {G : Type*} [Group G] [Finite G]
    (actingGroup overgroup initialFirst initialSecond : Subgroup G)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup initialFirst)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup initialSecond)
    (hfirstEscape : ¬ initialFirst ≤ overgroup) (hsecondLe : initialSecond ≤ overgroup) :
    ∃ first second : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup first ∧
      rankTwoMaximalInvariantTwoSubgroup actingGroup second ∧
      ¬ first ≤ overgroup ∧ second ≤ overgroup ∧
      Nat.card (initialFirst ⊓ initialSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G) ∧
      ∀ largerFirst largerSecond : Subgroup G,
        rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
        rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
        ¬ largerFirst ≤ overgroup → largerSecond ≤ overgroup →
        Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G) := by
  let pairs := {pair : Subgroup G × Subgroup G //
    rankTwoMaximalInvariantTwoSubgroup actingGroup pair.1 ∧
    rankTwoMaximalInvariantTwoSubgroup actingGroup pair.2 ∧
    ¬ pair.1 ≤ overgroup ∧ pair.2 ≤ overgroup}
  let initialPair : pairs := ⟨⟨initialFirst, initialSecond⟩,
    hfirst, hsecond, hfirstEscape, hsecondLe⟩
  let : Nonempty pairs := ⟨initialPair⟩
  obtain ⟨maximalPair, hmaximal⟩ := Finite.exists_max
    (fun pair : pairs => Nat.card (pair.val.1 ⊓ pair.val.2 : Subgroup G))
  exact ⟨maximalPair.val.1, maximalPair.val.2, maximalPair.property.1,
    maximalPair.property.2.1, maximalPair.property.2.2.1, maximalPair.property.2.2.2,
    hmaximal initialPair, fun first second hfirst hsecond hescape hcontained =>
      hmaximal ⟨⟨first, second⟩, hfirst, hsecond, hescape, hcontained⟩⟩

theorem relative_pair_intersection_normalizer_escapes
    {G : Type*} [Group G] [Finite G] (overgroup first second : Subgroup G)
    (hfirstGroup : IsPGroup 2 first) (hfirstEscape : ¬ first ≤ overgroup)
    (hsecondLe : second ≤ overgroup)
    (hintersection : first ⊓ overgroup = first ⊓ second) :
    ¬ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) ≤ overgroup := by
  have hproper : first ⊓ second < first := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hequal
    exact hfirstEscape (hequal.symm.le.trans (inf_le_right.trans hsecondLe))
  have hgrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    first (first ⊓ second) hfirstGroup hproper
  intro hnormalizer
  have hbound : first ⊓ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) ≤
      first ⊓ second := by
    exact (inf_le_inf_left first hnormalizer).trans hintersection.le
  exact hgrows.not_ge hbound

theorem relative_maximal_pair_intersection_normalizer_not_prime_constrained
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup overgroup first second : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hacting : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstEscape : ¬ first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hintersection : first ⊓ overgroup = first ⊓ second)
    (hcentralizer : Subgroup.centralizer (actingGroup : Set G) ≤ overgroup)
    (hmaximal : ∀ largerFirst largerSecond : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
      ¬ largerFirst ≤ overgroup → largerSecond ≤ overgroup →
      Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G))
    (hglobalize : ∀ localSecond : Subgroup G,
      invariantTwoMaximalWithin actingGroup overgroup localSecond →
      rankTwoMaximalInvariantTwoSubgroup actingGroup localSecond)
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    ¬ HasPrimeConstraint (G := Subgroup.normalizer
      ((first ⊓ second : Subgroup G) : Set G)) prime := by
  let intersection := first ⊓ second
  let localGroup := Subgroup.normalizer (intersection : Set G)
  have hlocalActor : actingGroup ≤ localGroup := common_normalizer_le_normalizer_inf
    actingGroup first second hfirst.2.1 hsecond.2.1
  have hproper : intersection < first := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hequal
    exact hfirstEscape (hequal.symm.le.trans (inf_le_right.trans hsecondLe))
  have hgrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    first intersection hfirst.1 hproper
  have hfirstNormalizingEscape : ¬ first ⊓ localGroup ≤ overgroup := by
    intro hbound
    have hsmaller : first ⊓ localGroup ≤ intersection := by
      change first ⊓ localGroup ≤ first ⊓ second
      rw [← hintersection]
      exact le_inf inf_le_left hbound
    exact hgrows.not_ge hsmaller
  obtain ⟨firstLocal, hfirstLe, hfirstLocal⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup localGroup (first ⊓ localGroup) inf_le_right hfirst.1.to_inf_left
    (invariant_normalizer_intersection actingGroup first second hfirst.2.1 hsecond.2.1)
  obtain ⟨secondLocal, hsecondLeLocal, hsecondLocal⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup localGroup (second ⊓ localGroup) inf_le_right hsecond.1.to_inf_left (by
      simpa only [localGroup, intersection, inf_comm second first] using
        invariant_normalizer_intersection actingGroup second first hsecond.2.1 hfirst.2.1)
  intro hconstraint
  obtain ⟨conjugator, hconjugatorLocal, hconjugatorCentral, hconjugate⟩ :=
    invariantTwoMaximalWithin_constrained_transitivity prime hprime hodd actingGroup localGroup
      firstLocal secondLocal hactor hlocalActor hconstraint hfirstLocal hsecondLocal
      (fun element _helement hcentral horder => hcontains element hcentral horder)
  have hfirstLocalEscape : ¬ firstLocal ≤ overgroup :=
    fun hbound => hfirstNormalizingEscape (hfirstLe.trans hbound)
  have hsecondLocalEscape : ¬ secondLocal ≤ overgroup := by
    intro hbound
    exact hfirstLocalEscape ((conjugate_subgroup_le_iff_of_conjugator_mem firstLocal overgroup
      conjugator (hcentralizer hconjugatorCentral)).mp (hconjugate.le.trans hbound))
  obtain ⟨largerFirst, hsecondLocalLe, hlargerFirst⟩ := exists_maximal_invariant_two_subgroup_containing
    actingGroup secondLocal hsecondLocal.2.1 hsecondLocal.2.2.1
  have hlargerFirstEscape : ¬ largerFirst ≤ overgroup :=
    fun hbound => hsecondLocalEscape (hsecondLocalLe.trans hbound)
  let commonInside := secondLocal ⊓ overgroup
  have hcommonInvariant : actingGroup ≤ Subgroup.normalizer (commonInside : Set G) :=
    common_normalizer_le_normalizer_inf actingGroup secondLocal overgroup
      hsecondLocal.2.2.1 (hacting.trans Subgroup.le_normalizer)
  obtain ⟨largerSecond, hcommonLe, hlargerSecondWithin⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup overgroup commonInside inf_le_right hsecondLocal.2.1.to_inf_left hcommonInvariant
  have hlargerSecond := hglobalize largerSecond hlargerSecondWithin
  have hbound := hmaximal largerFirst largerSecond hlargerFirst hlargerSecond
    hlargerFirstEscape hlargerSecondWithin.1
  have hcommonLeBoth : commonInside ≤ largerFirst ⊓ largerSecond :=
    le_inf (inf_le_left.trans hsecondLocalLe) hcommonLe
  have hsmall := Subgroup.card_le_of_le hcommonLeBoth
  have hintersectionLeCommon : intersection ≤ commonInside := by
    exact le_inf ((le_inf inf_le_right Subgroup.le_normalizer).trans hsecondLeLocal)
      (inf_le_right.trans hsecondLe)
  have hcommonEq := Subgroup.eq_of_le_of_card_ge hintersectionLeCommon (hsmall.trans hbound)
  have hsecondLocalNormalizerLe : second ⊓ localGroup ≤ intersection := by
    rw [hcommonEq]
    exact le_inf hsecondLeLocal (inf_le_left.trans hsecondLe)
  have hsecondProper : intersection < second := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro hequal
    have hsecondContained : second ≤ first := hequal.symm.le.trans inf_le_left
    have hequalGroups := hsecond.2.2 first hfirst.1 hfirst.2.1 hsecondContained
    exact hfirstEscape (hequalGroups.le.trans hsecondLe)
  have hsecondGrows := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    second intersection hsecond.1 hsecondProper
  exact hsecondGrows.not_ge hsecondLocalNormalizerLe

end CFSG.RankThreeCoreUniqueness.Helpers
