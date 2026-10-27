module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CriticalReduction

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem normal_self_centralizing_core_signalizer_eq_bot
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (valueGroup : Subgroup G) (hnormal : valueGroup.Normal)
    (hvalue : IsPGroup prime valueGroup)
    (hconstraint : Subgroup.centralizer (valueGroup : Set G) ≤ valueGroup)
    (actingGroup signalizer : Subgroup G) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) : signalizer = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : valueGroup.Normal := hnormal
  have hcoprime : (Nat.card valueGroup).Coprime (Nat.card signalizer) := by
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hvalue
    rw [hcard]
    exact hsignalizer.pow_left exponent
  have hdisjoint : Disjoint valueGroup signalizer :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  let actorAction := ambientSubgroupActionHom actingGroup valueGroup
    (show actingGroup ≤ Subgroup.normalizer (valueGroup : Set G) by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  let signalizerAction := ambientSubgroupActionHom signalizer valueGroup
    (show signalizer ≤ Subgroup.normalizer (valueGroup : Set G) by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  let normalizingAction := ambientSubgroupActionHom actingGroup signalizer hinvariant
  let : MulDistribMulAction actingGroup valueGroup :=
    multiplicativeActionOfMulAutHom actorAction
  let : MulDistribMulAction signalizer valueGroup :=
    multiplicativeActionOfMulAutHom signalizerAction
  have hcompatibility : ∀ actingElement : actingGroup, ∀ otherElement : signalizer,
      ∀ element : valueGroup,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element := by
    intro actingElement otherElement element
    apply Subtype.ext
    change (actorAction actingElement (signalizerAction otherElement element) : G) =
      (signalizerAction (normalizingAction actingElement otherElement)
        (actorAction actingElement element) : G)
    simp only [actorAction, signalizerAction, normalizingAction,
      ambientSubgroupActionHom_apply_coe]
    group
  have hfixedCentralized : ∀ element : valueGroup, element ^ prime = 1 →
      (∀ actingElement : actingGroup, actingElement • element = element) →
      ∀ otherElement : signalizer, otherElement • element = element := by
    intro element hpower hfixed otherElement
    have helementCentralizes : (element : G) ∈ Subgroup.centralizer (actingGroup : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro actingElement hactingElement
      have hequality := congrArg Subtype.val (hfixed ⟨actingElement, hactingElement⟩)
      change actingElement * (element : G) * actingElement⁻¹ = element at hequality
      have hcancel := congrArg (fun value : G => value * actingElement) hequality
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    have helementActor : (element : G) ∈ actingGroup := by
      by_cases helementOne : (element : G) = 1
      · exact helementOne ▸ actingGroup.one_mem
      · exact hcontains element helementCentralizes
          (orderOf_eq_prime (congrArg Subtype.val hpower) helementOne)
    have hcommutator : (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
        (element : G)⁻¹ ∈ valueGroup ⊓ signalizer := by
      constructor
      · exact valueGroup.mul_mem (hnormal.conj_mem element element.property otherElement)
          (valueGroup.inv_mem element.property)
      · have hconjugate := Subgroup.le_normalizer_iff.mp hinvariant element helementActor
          (otherElement : G)⁻¹ (signalizer.inv_mem otherElement.property)
        have hproduct := signalizer.mul_mem otherElement.property hconjugate
        change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
          (element : G)⁻¹ ∈ signalizer
        simpa only [mul_assoc] using hproduct
    have hcommutatorOne : (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
        (element : G)⁻¹ = 1 := by
      rw [hdisjoint.eq_bot] at hcommutator
      exact Subgroup.mem_bot.mp hcommutator
    apply Subtype.ext
    change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ = element
    have hcancel := congrArg (fun value : G => value * (element : G)) hcommutatorOne
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hcancel
  have hresult := odd_pGroup_normalized_actor_fixed_order_prime_lemma
    prime hprime hodd hactor hvalue hcoprime normalizingAction hcompatibility
    hfixedCentralized
  have hcentralizes : signalizer ≤ Subgroup.centralizer (valueGroup : Set G) := by
    intro otherElement hotherElement
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    have hequality := congrArg Subtype.val
      (hresult ⟨otherElement, hotherElement⟩ ⟨element, helement⟩)
    change otherElement * element * otherElement⁻¹ = element at hequality
    have hcancel := congrArg (fun value : G => value * otherElement) hequality
    have hequal : otherElement * element = element * otherElement := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    exact hequal.symm
  have hcontained := hcentralizes.trans hconstraint
  apply le_bot_iff.mp
  intro element helement
  rw [← hdisjoint.eq_bot]
  exact ⟨hcontained helement, helement⟩

theorem quotient_self_centralizing_core_signalizer_le_kernel
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target] [Finite Target]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (homomorphism : Source →* Target) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (valueGroup : Subgroup Target) (hnormal : valueGroup.Normal)
    (hvalue : IsPGroup prime valueGroup)
    (hconstraint : Subgroup.centralizer (valueGroup : Set Target) ≤ valueGroup)
    (actingGroup signalizer : Subgroup Source) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set Source))
    (hcontains : ∀ element : Source,
      element ∈ Subgroup.centralizer (actingGroup : Set Source) →
      orderOf element = prime → element ∈ actingGroup) :
    signalizer ≤ homomorphism.ker := by
  have himageCoprime : prime.Coprime (Nat.card (signalizer.map homomorphism)) := by
    exact hsignalizer.of_dvd_right
      (CFSG.card_dvd_of_surjective
        (homomorphism.subgroupMap signalizer) (homomorphism.subgroupMap_surjective signalizer))
  have himageInvariant : actingGroup.map homomorphism ≤
      Subgroup.normalizer (signalizer.map homomorphism : Set Target) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actingElement ⟨actingPreimage, hactingPreimage, rfl⟩
      element ⟨preimage, hpreimage, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem homomorphism
      (Subgroup.le_normalizer_iff.mp hinvariant actingPreimage hactingPreimage preimage hpreimage)
  have htrivial := normal_self_centralizing_core_signalizer_eq_bot prime hprime hodd valueGroup
    hnormal hvalue hconstraint (actingGroup.map homomorphism)
    (signalizer.map homomorphism) (hactor.map homomorphism) himageCoprime himageInvariant
    (coprime_quotient_preserves_order_prime_centralizer_condition prime hprime
      actingGroup hactor homomorphism hsurjective hkernel hcontains)
  intro element helement
  apply MonoidHom.mem_ker.mpr
  have himage := Subgroup.mem_map_of_mem homomorphism helement
  rw [htrivial] at himage
  exact Subgroup.mem_bot.mp himage

end CFSG.RankThreeCoreUniqueness.Helpers
