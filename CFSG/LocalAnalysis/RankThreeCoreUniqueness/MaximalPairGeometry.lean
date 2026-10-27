module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def actorCentralizerConjugate {G : Type*} [Group G]
    (actingGroup first second : Subgroup G) : Prop :=
  ∃ conjugator : G, conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
    Subgroup.map (MulAut.conj conjugator).toMonoidHom first = second

theorem actorCentralizerConjugate_refl
    {G : Type*} [Group G] (actingGroup subgroup : Subgroup G) :
    actorCentralizerConjugate actingGroup subgroup subgroup := by
  refine ⟨1, (Subgroup.centralizer (actingGroup : Set G)).one_mem, ?_⟩
  have hidentity : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext element
    simp
  rw [hidentity, Subgroup.map_id]

theorem actorCentralizerConjugate_symm
    {G : Type*} [Group G] {actingGroup first second : Subgroup G}
    (hconjugate : actorCentralizerConjugate actingGroup first second) :
    actorCentralizerConjugate actingGroup second first := by
  obtain ⟨conjugator, hcentral, hequal⟩ := hconjugate
  refine ⟨conjugator⁻¹, (Subgroup.centralizer (actingGroup : Set G)).inv_mem hcentral, ?_⟩
  rw [← hequal, conjugate_map_mul]
  have hidentity : (MulAut.conj (conjugator⁻¹ * conjugator)).toMonoidHom = MonoidHom.id G := by
    ext element
    simp
  rw [hidentity, Subgroup.map_id]

theorem actorCentralizerConjugate_trans
    {G : Type*} [Group G] {actingGroup first middle last : Subgroup G}
    (hfirst : actorCentralizerConjugate actingGroup first middle)
    (hsecond : actorCentralizerConjugate actingGroup middle last) :
    actorCentralizerConjugate actingGroup first last := by
  obtain ⟨firstConjugator, hfirstCentral, hfirstMap⟩ := hfirst
  obtain ⟨secondConjugator, hsecondCentral, hsecondMap⟩ := hsecond
  refine ⟨secondConjugator * firstConjugator,
    (Subgroup.centralizer (actingGroup : Set G)).mul_mem hsecondCentral hfirstCentral, ?_⟩
  rw [← conjugate_map_mul, hfirstMap, hsecondMap]

theorem pGroup_proper_subgroup_lt_internal_normalizer
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (primeGroup subgroup : Subgroup G) (hpGroup : IsPGroup prime primeGroup)
    (hproper : subgroup < primeGroup) :
    subgroup < primeGroup ⊓ Subgroup.normalizer (subgroup : Set G) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent primeGroup := hpGroup.isNilpotent
  have hinternalProper : subgroup.subgroupOf primeGroup < ⊤ := by
    exact lt_top_iff_ne_top.mpr (fun htop =>
      hproper.not_ge (Subgroup.subgroupOf_eq_top.mp htop))
  have hinternal := Group.normalizerCondition_of_isNilpotent
    (subgroup.subgroupOf primeGroup) hinternalProper
  have hmapped := Subgroup.map_subtype_lt_map_subtype.mpr hinternal
  rw [Subgroup.map_subgroupOf_eq_of_le hproper.le,
    ← Subgroup.subgroupOf_normalizer_eq hproper.le] at hmapped
  have hnormalizerMap : Subgroup.map primeGroup.subtype
      ((Subgroup.normalizer (subgroup : Set G)).subgroupOf primeGroup) =
      primeGroup ⊓ Subgroup.normalizer (subgroup : Set G) := by
    rw [← Subgroup.inf_subgroupOf_right, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      inf_comm]
  rwa [hnormalizerMap] at hmapped

theorem invariant_normalizer_intersection
    {G : Type*} [Group G] (actingGroup first second : Subgroup G)
    (hfirst : actingGroup ≤ Subgroup.normalizer (first : Set G))
    (hsecond : actingGroup ≤ Subgroup.normalizer (second : Set G)) :
    actingGroup ≤ Subgroup.normalizer
      ((first ⊓ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hintersection := common_normalizer_le_normalizer_inf actingGroup first second hfirst hsecond
  have hnormalizer := hintersection.trans
    (Subgroup.le_normalizer (H := Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G)))
  exact common_normalizer_le_normalizer_inf actingGroup _ _ hfirst hnormalizer

theorem exists_maximal_nonconjugate_invariant_pair
    {G : Type*} [Group G] [Finite G] (actingGroup initialFirst initialSecond : Subgroup G)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup initialFirst)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup initialSecond)
    (hnonconjugate : ¬ actorCentralizerConjugate actingGroup initialFirst initialSecond) :
    ∃ first second : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup first ∧
      rankTwoMaximalInvariantTwoSubgroup actingGroup second ∧
      ¬ actorCentralizerConjugate actingGroup first second ∧
      Nat.card (initialFirst ⊓ initialSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G) ∧
      ∀ largerFirst largerSecond : Subgroup G,
        rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
        rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
        ¬ actorCentralizerConjugate actingGroup largerFirst largerSecond →
        Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G) := by
  let pairs := {pair : Subgroup G × Subgroup G //
    rankTwoMaximalInvariantTwoSubgroup actingGroup pair.1 ∧
    rankTwoMaximalInvariantTwoSubgroup actingGroup pair.2 ∧
    ¬ actorCentralizerConjugate actingGroup pair.1 pair.2}
  let initialPair : pairs := ⟨⟨initialFirst, initialSecond⟩, hfirst, hsecond, hnonconjugate⟩
  let : Nonempty pairs := ⟨initialPair⟩
  obtain ⟨maximalPair, hmaximal⟩ := Finite.exists_max
    (fun pair : pairs => Nat.card (pair.val.1 ⊓ pair.val.2 : Subgroup G))
  exact ⟨maximalPair.val.1, maximalPair.val.2, maximalPair.property.1,
    maximalPair.property.2.1, maximalPair.property.2.2, hmaximal initialPair,
    fun first second hfirst hsecond hnot => hmaximal ⟨⟨first, second⟩, hfirst, hsecond, hnot⟩⟩

theorem maximal_pair_intersection_normalizer_twoLocal
    {G : Type*} [Group G] (actingGroup first second : Subgroup G)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hnontrivial : first ⊓ second ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G)) ∧
      actingGroup ≤ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) :=
  ⟨⟨_, hnontrivial, hfirst.1.to_inf_left, rfl⟩,
    common_normalizer_le_normalizer_inf actingGroup first second hfirst.2.1 hsecond.2.1⟩

theorem maximal_pair_intersection_normalizer_not_prime_constrained
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup first second : Subgroup G)
    (hactor : IsPGroup prime actingGroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hnonconjugate : ¬ actorCentralizerConjugate actingGroup first second)
    (hmaximal : ∀ largerFirst largerSecond : Subgroup G,
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerFirst →
      rankTwoMaximalInvariantTwoSubgroup actingGroup largerSecond →
      ¬ actorCentralizerConjugate actingGroup largerFirst largerSecond →
      Nat.card (largerFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card (first ⊓ second : Subgroup G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G) →
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    ¬ HasPrimeConstraint (G := Subgroup.normalizer
      ((first ⊓ second : Subgroup G) : Set G)) prime := by
  let intersection := first ⊓ second
  let localGroup := Subgroup.normalizer (intersection : Set G)
  have hacting : actingGroup ≤ localGroup :=
    common_normalizer_le_normalizer_inf actingGroup first second hfirst.2.1 hsecond.2.1
  have hfirstProper : intersection < first := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hequal
    have hbound : first ≤ second := hequal.symm.le.trans inf_le_right
    have hequalGroups := hfirst.2.2 second hsecond.1 hsecond.2.1 hbound
    exact hnonconjugate (hequalGroups ▸ actorCentralizerConjugate_refl actingGroup first)
  have hnormalizerGrow := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    first intersection hfirst.1 hfirstProper
  have hsecondProper : intersection < second := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro hequal
    have hbound : second ≤ first := hequal.symm.le.trans inf_le_left
    have hequalGroups := hsecond.2.2 first hfirst.1 hfirst.2.1 hbound
    exact hnonconjugate (hequalGroups ▸ actorCentralizerConjugate_refl actingGroup second)
  have hsecondNormalizerGrow := pGroup_proper_subgroup_lt_internal_normalizer 2 Nat.prime_two
    second intersection hsecond.1 hsecondProper
  have hfirstCardGrow : Nat.card intersection < Nat.card (first ⊓ localGroup : Subgroup G) := by
    apply lt_of_not_ge
    intro hcard
    exact hnormalizerGrow.ne (Subgroup.eq_of_le_of_card_ge hnormalizerGrow.le hcard)
  have hsecondCardGrow : Nat.card intersection < Nat.card (second ⊓ localGroup : Subgroup G) := by
    apply lt_of_not_ge
    intro hcard
    exact hsecondNormalizerGrow.ne (Subgroup.eq_of_le_of_card_ge hsecondNormalizerGrow.le hcard)
  obtain ⟨firstLocal, hfirstLe, hfirstLocal⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup localGroup (first ⊓ localGroup) inf_le_right hfirst.1.to_inf_left
    (invariant_normalizer_intersection actingGroup first second hfirst.2.1 hsecond.2.1)
  obtain ⟨secondLocal, hsecondLe, hsecondLocal⟩ := exists_invariantTwoMaximalWithin_containing
    actingGroup localGroup (second ⊓ localGroup) inf_le_right hsecond.1.to_inf_left (by
      simpa only [localGroup, intersection, inf_comm second first] using
        invariant_normalizer_intersection actingGroup second first hsecond.2.1 hfirst.2.1)
  intro hconstraint
  obtain ⟨conjugator, hlocal, hcentral, hmaps⟩ :=
    invariantTwoMaximalWithin_constrained_transitivity prime hprime hodd actingGroup localGroup
      firstLocal secondLocal hactor hacting hconstraint hfirstLocal hsecondLocal hcontains
  obtain ⟨largerFirst, hfirstLocalLe, hlargerFirst⟩ :=
    exists_maximal_invariant_two_subgroup_containing actingGroup firstLocal
      hfirstLocal.2.1 hfirstLocal.2.2.1
  obtain ⟨largerSecond, hsecondLocalLe, hlargerSecond⟩ :=
    exists_maximal_invariant_two_subgroup_containing actingGroup secondLocal
      hsecondLocal.2.1 hsecondLocal.2.2.1
  have hintersectionFirst : intersection ≤ largerFirst :=
    (le_inf inf_le_left Subgroup.le_normalizer).trans (hfirstLe.trans hfirstLocalLe)
  have hintersectionSecond : intersection ≤ largerSecond :=
    (le_inf inf_le_right Subgroup.le_normalizer).trans (hsecondLe.trans hsecondLocalLe)
  have hfirstConjugate : actorCentralizerConjugate actingGroup first largerFirst := by
    by_contra hnot
    have hbound := hmaximal largerFirst first hlargerFirst hfirst (fun hconj =>
      hnot (actorCentralizerConjugate_symm hconj))
    have hintersectionBound : first ⊓ localGroup ≤ largerFirst ⊓ first :=
      le_inf (hfirstLe.trans hfirstLocalLe) inf_le_left
    have hsmall := Subgroup.card_le_of_le hintersectionBound
    change Nat.card (largerFirst ⊓ first : Subgroup G) ≤ Nat.card intersection at hbound
    omega
  have hsecondConjugate : actorCentralizerConjugate actingGroup second largerSecond := by
    by_contra hnot
    have hbound := hmaximal largerSecond second hlargerSecond hsecond (fun hconj =>
      hnot (actorCentralizerConjugate_symm hconj))
    have hintersectionBound : second ⊓ localGroup ≤ largerSecond ⊓ second :=
      le_inf (hsecondLe.trans hsecondLocalLe) inf_le_left
    have hsmall := Subgroup.card_le_of_le hintersectionBound
    change Nat.card (largerSecond ⊓ second : Subgroup G) ≤ Nat.card intersection at hbound
    omega
  let conjugateFirst := Subgroup.map (MulAut.conj conjugator).toMonoidHom largerFirst
  have hactorPreserved : Subgroup.map (MulAut.conj conjugator).toMonoidHom actingGroup = actingGroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer (actingGroup : Set G) hcentral)
  have hconjugateMaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup conjugateFirst := by
    have hmap := rankTwoMaximalInvariantTwoSubgroup_map actingGroup largerFirst
      (MulAut.conj conjugator) hlargerFirst
    rwa [hactorPreserved] at hmap
  have hsecondLocalConjugate : secondLocal ≤ conjugateFirst := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hfirstLocalLe
    rwa [hmaps] at hmap
  have hconjugatePair : actorCentralizerConjugate actingGroup conjugateFirst largerSecond := by
    by_contra hnot
    have hbound := hmaximal conjugateFirst largerSecond hconjugateMaximal hlargerSecond hnot
    have hsmall := Subgroup.card_le_of_le
      (hsecondLe.trans (le_inf hsecondLocalConjugate hsecondLocalLe))
    change Nat.card (conjugateFirst ⊓ largerSecond : Subgroup G) ≤ Nat.card intersection at hbound
    omega
  have hfirstToConjugate : actorCentralizerConjugate actingGroup largerFirst conjugateFirst :=
    ⟨conjugator, hcentral, rfl⟩
  exact hnonconjugate (actorCentralizerConjugate_trans hfirstConjugate
    (actorCentralizerConjugate_trans hfirstToConjugate
      (actorCentralizerConjugate_trans hconjugatePair (actorCentralizerConjugate_symm hsecondConjugate))))

end CFSG.RankThreeCoreUniqueness.Helpers
