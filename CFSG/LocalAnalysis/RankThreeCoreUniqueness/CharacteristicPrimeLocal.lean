module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance

public section

open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem self_centralizing_pCore_normalizer
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (actingGroup : Subgroup G) (hacting : IsPGroup prime actingGroup) :
    Subgroup.centralizer
        (pCore prime (Subgroup.normalizer (actingGroup : Set G)) :
          Set (Subgroup.normalizer (actingGroup : Set G))) ≤
      pCore prime (Subgroup.normalizer (actingGroup : Set G)) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let localGroup := Subgroup.normalizer (actingGroup : Set G)
  let core := pCore prime G
  let : core.Normal := pCore_normal prime
  let centralGroup := localGroup ⊓ Subgroup.centralizer (pCoreOf prime localGroup : Set G)
  have hactingCore : actingGroup ≤ pCoreOf prime localGroup :=
    normal_pGroup_le_pCoreOf prime actingGroup localGroup Subgroup.le_normalizer
      Subgroup.normal_in_normalizer hacting
  have hintersectionNormal : ((core ⊓ localGroup).subgroupOf localGroup).Normal := by
    have heq : (core ⊓ localGroup).subgroupOf localGroup = core.subgroupOf localGroup := by
      ext element
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, element.property, and_true]
    rw [heq]
    infer_instance
  have hintersectionCore : core ⊓ localGroup ≤ pCoreOf prime localGroup :=
    normal_pGroup_le_pCoreOf prime _ localGroup inf_le_right hintersectionNormal
      ((pCore_isPGroup prime).to_le inf_le_left)
  have hfixedCore : core ⊓ Subgroup.centralizer (actingGroup : Set G) ≤
      pCoreOf prime localGroup :=
    (le_inf inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))).trans hintersectionCore
  have hcentralPGroup : IsPGroup prime centralGroup := by
    apply IsPGroup.of_card (n := (Nat.card centralGroup).primeFactorsList.length)
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro divisor hdivisor hdivides
    by_contra hdifferent
    let : Fact divisor.Prime := ⟨hdivisor⟩
    obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' divisor hdivides
    let otherGroup := Subgroup.zpowers (element : G)
    have hother : IsPGroup divisor otherGroup := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, horder, pow_one]
    have hotherLocal : otherGroup ≤ localGroup :=
      Subgroup.zpowers_le.mpr element.property.1
    have hotherCentral : otherGroup ≤ Subgroup.centralizer (pCoreOf prime localGroup : Set G) :=
      Subgroup.zpowers_le.mpr element.property.2
    have hcoprime : (Nat.card core).Coprime (Nat.card otherGroup) :=
      IsPGroup.coprime_card_of_ne prime divisor (fun heq => hdifferent heq.symm) core otherGroup
        (pCore_isPGroup prime) hother
    have hotherCore : otherGroup ≤ core :=
      (ambient_subgroup_axb_centralizer_le prime hprime actingGroup otherGroup core
        hacting (pCore_isPGroup prime) hcoprime
        Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal
        (hotherCentral.trans (Subgroup.centralizer_le hactingCore))
        (hotherCentral.trans (Subgroup.centralizer_le hfixedCore))).trans hcharacteristic
    have hdisjoint := IsPGroup.disjoint_of_ne divisor prime hdifferent otherGroup core
      hother (pCore_isPGroup prime)
    have hotherBot : otherGroup = ⊥ := by
      apply le_bot_iff.mp
      exact (le_inf le_rfl hotherCore).trans (disjoint_iff.mp hdisjoint).le
    have helementOne : (element : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hotherBot]
      exact Subgroup.mem_zpowers _
    have horderOne : orderOf element = 1 := by
      rw [← Subgroup.orderOf_coe element, helementOne, orderOf_one]
    exact hdivisor.ne_one (horder.symm.trans horderOne)
  have hcentralNormalizes : localGroup ≤
      Subgroup.normalizer (Subgroup.centralizer (pCoreOf prime localGroup : Set G) : Set G) :=
    (localGroup_le_normalizer_pCoreOf prime localGroup).trans
      (normalizer_le_normalizer_centralizer (pCoreOf prime localGroup))
  have hcentralCore : centralGroup ≤ pCoreOf prime localGroup :=
    normal_pGroup_le_pCoreOf prime centralGroup localGroup inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (common_normalizer_le_normalizer_inf localGroup localGroup
          (Subgroup.centralizer (pCoreOf prime localGroup : Set G))
          Subgroup.le_normalizer hcentralNormalizes)) hcentralPGroup
  intro element helement
  have hambient : element.val ∈ Subgroup.centralizer (pCoreOf prime localGroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro member ⟨preimage, hpreimage, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp helement preimage hpreimage)
  have hcore : element ∈ (pCoreOf prime localGroup).subgroupOf localGroup :=
    hcentralCore ⟨element.property, hambient⟩
  rwa [pCoreOf_subgroupOf] at hcore

theorem self_centralizing_pCore_centralizer
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (actingGroup : Subgroup G) (hacting : IsPGroup prime actingGroup) :
    Subgroup.centralizer
        (pCore prime (Subgroup.centralizer (actingGroup : Set G)) :
          Set (Subgroup.centralizer (actingGroup : Set G))) ≤
      pCore prime (Subgroup.centralizer (actingGroup : Set G)) := by
  exact normal_subgroupOf_self_centralizing_pCore prime hprime
    (Subgroup.centralizer (actingGroup : Set G))
    (Subgroup.normalizer (actingGroup : Set G))
    (Subgroup.centralizer_le_normalizer _) (by infer_instance)
    (self_centralizing_pCore_normalizer prime hprime hcharacteristic actingGroup hacting)

end CFSG.RankThreeCoreUniqueness.Helpers
