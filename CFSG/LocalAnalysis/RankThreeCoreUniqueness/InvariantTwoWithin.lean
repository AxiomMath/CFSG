module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def invariantTwoMaximalWithin {G : Type*} [Group G]
    (actingGroup overgroup twoGroup : Subgroup G) : Prop :=
  twoGroup ≤ overgroup ∧ IsPGroup 2 twoGroup ∧
    actingGroup ≤ Subgroup.normalizer (twoGroup : Set G) ∧
    ∀ larger : Subgroup G, larger ≤ overgroup → IsPGroup 2 larger →
      actingGroup ≤ Subgroup.normalizer (larger : Set G) → twoGroup ≤ larger → larger = twoGroup

theorem exists_invariantTwoMaximalWithin_containing
    {G : Type*} [Group G] [Finite G] (actingGroup overgroup twoGroup : Subgroup G)
    (hcontained : twoGroup ≤ overgroup) (htwo : IsPGroup 2 twoGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (twoGroup : Set G)) :
    ∃ maximalGroup : Subgroup G, twoGroup ≤ maximalGroup ∧
      invariantTwoMaximalWithin actingGroup overgroup maximalGroup := by
  obtain ⟨maximalGroup, hbound, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => subgroup ≤ overgroup ∧ IsPGroup 2 subgroup ∧
      actingGroup ≤ Subgroup.normalizer (subgroup : Set G)) ⟨hcontained, htwo, hinvariant⟩
  exact ⟨maximalGroup, hbound, hmaximal.prop.1, hmaximal.prop.2.1, hmaximal.prop.2.2,
    fun _ hle hgroup hnormalized hcontains =>
      (hmaximal.eq_of_le ⟨hle, hgroup, hnormalized⟩ hcontains).symm⟩

theorem invariantTwoMaximalWithin_internal_global
    {G : Type*} [Group G] (actingGroup overgroup twoGroup : Subgroup G)
    (hacting : actingGroup ≤ overgroup)
    (hmaximal : invariantTwoMaximalWithin actingGroup overgroup twoGroup) :
    rankTwoMaximalInvariantTwoSubgroup (actingGroup.subgroupOf overgroup)
      (twoGroup.subgroupOf overgroup) := by
  have hinternalGroup := hmaximal.2.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe hmaximal.1).symm
  have hinternalInvariant : actingGroup.subgroupOf overgroup ≤
      Subgroup.normalizer (twoGroup.subgroupOf overgroup : Set overgroup) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hmaximal.1]
    intro element helement
    exact hmaximal.2.2.1 helement
  refine ⟨hinternalGroup, hinternalInvariant, ?_⟩
  intro larger hgroup hinvariant hcontains
  have himageInvariant : actingGroup ≤
      Subgroup.normalizer (Subgroup.map overgroup.subtype larger : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actingElement hactingElement value ⟨preimage, hpreimage, rfl⟩
    let internalActor : overgroup := ⟨actingElement, hacting hactingElement⟩
    have hconjugate := Subgroup.le_normalizer_iff.mp hinvariant internalActor hactingElement
      preimage hpreimage
    exact Subgroup.mem_map_of_mem overgroup.subtype hconjugate
  have himageContains := Subgroup.map_mono (f := overgroup.subtype) hcontains
  rw [Subgroup.map_subgroupOf_eq_of_le hmaximal.1] at himageContains
  have hequal := hmaximal.2.2.2 (Subgroup.map overgroup.subtype larger)
    (Subgroup.map_subtype_le _) (hgroup.map overgroup.subtype) himageInvariant himageContains
  apply Subgroup.map_injective overgroup.subtype_injective
  exact hequal.trans (Subgroup.map_subgroupOf_eq_of_le hmaximal.1).symm

theorem invariantTwoMaximalWithin_constrained_transitivity
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup overgroup first second : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hacting : actingGroup ≤ overgroup)
    (hconstraint : HasPrimeConstraint (G := overgroup) prime)
    (hfirst : invariantTwoMaximalWithin actingGroup overgroup first)
    (hsecond : invariantTwoMaximalWithin actingGroup overgroup second)
    (hcontains : ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    ∃ conjugator : G, conjugator ∈ overgroup ∧
      conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
      Subgroup.map (MulAut.conj conjugator).toMonoidHom first = second := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hactorInternal := hactor.of_equiv (Subgroup.subgroupOfEquivOfLe hacting).symm
  have hfirstInternal := invariantTwoMaximalWithin_internal_global actingGroup overgroup first
    hacting hfirst
  have hsecondInternal := invariantTwoMaximalWithin_internal_global actingGroup overgroup second
    hacting hsecond
  have hcontainsInternal : ∀ element : overgroup,
      element ∈ Subgroup.centralizer (actingGroup.subgroupOf overgroup : Set overgroup) →
      orderOf element = prime → element ∈ actingGroup.subgroupOf overgroup := by
    intro element hcentral horder
    apply hcontains element.val element.property
    · apply Subgroup.mem_centralizer_iff.mpr
      intro actor hactorMem
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentral
        ⟨actor, hacting hactorMem⟩ hactorMem)
    · exact (Subgroup.orderOf_coe element).trans horder
  have hcoprime (twoGroup : Subgroup overgroup) (htwo : IsPGroup 2 twoGroup) :
      prime.Coprime (Nat.card twoGroup) := by
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp htwo
    rw [hcard]
    exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right exponent
  have hfirstCore := prime_constraint_signalizer_le_primeComplementCore prime hprime hodd
    hconstraint (actingGroup.subgroupOf overgroup) (first.subgroupOf overgroup) hactorInternal
    (hcoprime _ hfirstInternal.1) hfirstInternal.2.1 hcontainsInternal
  have hsecondCore := prime_constraint_signalizer_le_primeComplementCore prime hprime hodd
    hconstraint (actingGroup.subgroupOf overgroup) (second.subgroupOf overgroup) hactorInternal
    (hcoprime _ hsecondInternal.1) hsecondInternal.2.1 hcontainsInternal
  obtain ⟨conjugator, hcentral, hequal⟩ :=
    rank_two_maximal_two_subgroups_common_signalizer_transitivity prime hprime
      (actingGroup.subgroupOf overgroup) (first.subgroupOf overgroup) (second.subgroupOf overgroup)
      (primeComplementCore prime) hactorInternal hfirstInternal hsecondInternal
      (primeComplementCore_coprime prime) (by
        rw [Subgroup.normalizer_eq_top]
        exact le_top)
      hfirstCore hsecondCore
  refine ⟨conjugator.val, conjugator.property, ?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro actor hactorMem
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentral
      ⟨actor, hacting hactorMem⟩ hactorMem)
  · have hmapped := congrArg (Subgroup.map overgroup.subtype) hequal
    have hmaps : overgroup.subtype.comp (MulAut.conj conjugator).toMonoidHom =
        (MulAut.conj conjugator.val).toMonoidHom.comp overgroup.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hfirst.1,
      Subgroup.map_subgroupOf_eq_of_le hsecond.1] at hmapped
    exact hmapped

end CFSG.RankThreeCoreUniqueness.Helpers
