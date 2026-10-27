module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal

public section

open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem prime_order_centralizer_local_characteristic
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcentralizers : ∀ element : G, orderOf element = prime →
      Subgroup.centralizer
          (pCore prime (Subgroup.centralizer ({element} : Set G)) :
            Set (Subgroup.centralizer ({element} : Set G))) ≤
        pCore prime (Subgroup.centralizer ({element} : Set G)))
    (actingGroup : Subgroup G) (hnontrivial : actingGroup ≠ ⊥)
    (hacting : IsPGroup prime actingGroup) :
    Subgroup.centralizer
        (pCore prime (Subgroup.normalizer (actingGroup : Set G)) :
          Set (Subgroup.normalizer (actingGroup : Set G))) ≤
      pCore prime (Subgroup.normalizer (actingGroup : Set G)) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Nontrivial actingGroup := actingGroup.nontrivial_iff_ne_bot.mpr hnontrivial
  let : Nontrivial (Subgroup.center actingGroup) := hacting.center_nontrivial
  have hcenterPrime : IsPGroup prime (Subgroup.center actingGroup) :=
    hacting.to_subgroup _
  have hcenterDivides : prime ∣ Nat.card (Subgroup.center actingGroup) := by
    obtain ⟨exponent, hpositive, hcard⟩ := hcenterPrime.nontrivial_iff_card.mp inferInstance
    rw [hcard]
    exact dvd_pow_self _ (Nat.ne_of_gt hpositive)
  obtain ⟨centralElement, hcentralOrder⟩ := exists_prime_orderOf_dvd_card' prime hcenterDivides
  let element : G := centralElement.val.val
  have horder : orderOf element = prime := by
    simpa only [element, Subgroup.orderOf_coe] using hcentralOrder
  let localGroup := Subgroup.normalizer (actingGroup : Set G)
  let centralizer := Subgroup.centralizer ({element} : Set G)
  have hactingCentralizes : actingGroup ≤ centralizer := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp centralElement.property (⟨member, hmember⟩ : actingGroup))
  let internalActor := actingGroup.subgroupOf centralizer
  have hinternalActor : IsPGroup prime internalActor :=
    hacting.of_equiv (Subgroup.subgroupOfEquivOfLe hactingCentralizes).symm
  let internalNormalizer := Subgroup.normalizer (internalActor : Set centralizer)
  have hinternalCharacteristic := self_centralizing_pCore_normalizer prime hprime
    (hcentralizers element horder) internalActor hinternalActor
  have hnormalizerMap : internalNormalizer.map centralizer.subtype =
      localGroup ⊓ centralizer := by
    have hcomap : localGroup.comap centralizer.subtype = internalNormalizer := by
      exact Subgroup.comap_normalizer_eq_of_le_range
        (hactingCentralizes.trans (le_of_eq centralizer.subtype_range.symm))
    rw [← hcomap]
    exact Subgroup.subgroupOf_map_subtype _ _
  let commonGroup := localGroup ⊓ centralizer
  have hcommonCharacteristic : Subgroup.centralizer (pCore prime commonGroup : Set commonGroup) ≤
      pCore prime commonGroup := by
    exact self_centralizing_pCore_of_mulEquiv prime
      ((internalNormalizer.equivMapOfInjective centralizer.subtype
        centralizer.subtype_injective).trans (MulEquiv.subgroupCongr hnormalizerMap))
      hinternalCharacteristic
  let core := pCore prime localGroup
  let : core.Characteristic := pCore_characteristic prime
  let : core.Normal := pCore_normal prime
  let coreCentralizer := Subgroup.centralizer (core : Set localGroup)
  let : coreCentralizer.Normal := by infer_instance
  let ambientCentralizer := coreCentralizer.map localGroup.subtype
  have hcentralizerLocal : ambientCentralizer ≤ localGroup := Subgroup.map_subtype_le _
  have hcentralizerCore : ambientCentralizer ≤
      Subgroup.centralizer (pCoreOf prime localGroup : Set G) := by
    rintro member ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro coreMember ⟨corePreimage, hcorePreimage, rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hpreimage corePreimage hcorePreimage)
  have hactingCore : actingGroup ≤ pCoreOf prime localGroup :=
    normal_pGroup_le_pCoreOf prime actingGroup localGroup Subgroup.le_normalizer
      Subgroup.normal_in_normalizer hacting
  have hcentralizerCommon : ambientCentralizer ≤ commonGroup := by
    refine le_inf hcentralizerLocal ?_
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hcentralizerCore hmember) element
        (hactingCore centralElement.val.property)).symm
  have hcentralizerNormal : (ambientCentralizer.subgroupOf commonGroup).Normal := by
    have hlocalNormal : (ambientCentralizer.subgroupOf localGroup).Normal := by
      have heq : ambientCentralizer.subgroupOf localGroup = coreCentralizer :=
        Subgroup.comap_map_eq_self_of_injective localGroup.subtype_injective _
      rw [heq]
      infer_instance
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hcentralizerCommon).mpr
    exact (inf_le_left : commonGroup ≤ localGroup).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hcentralizerLocal).mp hlocalNormal)
  have hcentralizerCharacteristic := normal_subgroupOf_self_centralizing_pCore prime hprime
    ambientCentralizer commonGroup hcentralizerCommon hcentralizerNormal hcommonCharacteristic
  have hlocalCharacteristic : Subgroup.centralizer
        (pCore prime coreCentralizer : Set coreCentralizer) ≤ pCore prime coreCentralizer :=
    self_centralizing_pCore_of_mulEquiv prime
      (coreCentralizer.equivMapOfInjective localGroup.subtype localGroup.subtype_injective).symm
      hcentralizerCharacteristic
  let internalCore := pCore prime coreCentralizer
  let : internalCore.Characteristic := pCore_characteristic prime
  let normalCore := internalCore.map coreCentralizer.subtype
  let : normalCore.Normal := by infer_instance
  have hnormalCoreLe : normalCore ≤ core :=
    normal_pGroup_le_pCore prime normalCore inferInstance
      ((pCore_isPGroup prime).map coreCentralizer.subtype)
  intro member hmember
  have hmemberCentral : (⟨member, hmember⟩ : coreCentralizer) ∈
      Subgroup.centralizer (internalCore : Set coreCentralizer) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro coreMember hcoreMember
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hmember coreMember.val
      (hnormalCoreLe (Subgroup.mem_map_of_mem coreCentralizer.subtype hcoreMember))
  exact hnormalCoreLe (Subgroup.mem_map_of_mem coreCentralizer.subtype
    (hlocalCharacteristic hmemberCentral))

end CFSG.RankThreeCoreUniqueness.Helpers
