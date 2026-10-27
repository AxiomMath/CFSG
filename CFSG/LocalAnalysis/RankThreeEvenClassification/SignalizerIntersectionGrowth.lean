module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PairwiseFixedGrowth
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedSylowConjugacy

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem SignalizerPrimeCompatible.inf {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (first second : Subgroup G)
    (hfirst : SignalizerPrimeCompatible prime subgroupPrime actor signalizer first)
    (hsecond : SignalizerPrimeCompatible prime subgroupPrime actor signalizer second) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer (first ⊓ second) :=
  SignalizerPrimeCompatible.of_le prime subgroupPrime actor signalizer first _ hfirst inf_le_left
    (normalizes_inf_of_normalizes_both actor first second hfirst.1.normalized hsecond.1.normalized)

theorem signalizer_prime_compatible_intersection_growth
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ) (hsubgroupPrime : subgroupPrime.Prime)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (first second : Subgroup G)
    (hfirst : SignalizerPrimeCompatible prime subgroupPrime actor signalizer first)
    (hsecond : SignalizerPrimeCompatible prime subgroupPrime actor signalizer second)
    (hfirstStrict : first ⊓ second < first) (hsecondStrict : first ⊓ second < second) :
    ∃ conjugator ∈ signalizerCommonFixed actor signalizer,
      ∃ maximal : Subgroup G,
        Maximal (SignalizerPrimeCompatible prime subgroupPrime actor signalizer) maximal ∧
        first ⊓ second < first.map (MulAut.conj conjugator).toMonoidHom ⊓ maximal ∧
        first ⊓ second < second ⊓ maximal := by
  let lower := first ⊓ second
  have hlowerCompatible := SignalizerPrimeCompatible.inf prime subgroupPrime actor signalizer
    first second hfirst hsecond
  obtain ⟨member, hmember, hmemberNe, hfirstGrowth, hsecondGrowth⟩ :=
    pairwise_normalizer_fixed_growth prime hprime subgroupPrime hsubgroupPrime actor first second
      hcomm hpower hcard hfirst.2 hsecond.2 hfirst.1.primeComplement hsecond.1.primeComplement
      hfirst.1.normalized hsecond.1.normalized hfirstStrict hsecondStrict
  let overgroup := Subgroup.normalizer (lower : Set G) ⊓ signalizer member
  have hvalueCompatible := signalizer_value_compatible prime hprime actor signalizer hsignalizer
    member hmember hmemberNe
  have hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G) :=
    normalizes_inf_of_normalizes_both actor _ _
      (hlowerCompatible.1.normalized.trans (normalizer_normalizes_normalizer lower))
      hvalueCompatible.normalized
  have hovergroupCompatible := SignalizerCompatible.of_le prime actor signalizer (signalizer member)
    overgroup hvalueCompatible inf_le_right hovergroupNormalized
  let firstPart := first ⊓ overgroup
  let secondPart := second ⊓ overgroup
  have hfirstPartNormalized : actor ≤ Subgroup.normalizer (firstPart : Set G) :=
    normalizes_inf_of_normalizes_both actor first overgroup hfirst.1.normalized hovergroupNormalized
  have hsecondPartNormalized : actor ≤ Subgroup.normalizer (secondPart : Set G) :=
    normalizes_inf_of_normalizes_both actor second overgroup hsecond.1.normalized hovergroupNormalized
  have hfirstPartPGroup : IsPGroup subgroupPrime firstPart := hfirst.2.to_le inf_le_left
  have hsecondPartPGroup : IsPGroup subgroupPrime secondPart := hsecond.2.to_le inf_le_left
  have hfirstNotLe : ¬firstPart ≤ lower := by
    intro hle
    apply hfirstGrowth
    intro element helement
    exact hle ⟨helement.1.1, helement.1.2,
      hfirst.1.fixed_le member hmember hmemberNe ⟨helement.1.1, helement.2⟩⟩
  have hsecondNotLe : ¬secondPart ≤ lower := by
    intro hle
    apply hsecondGrowth
    intro element helement
    exact hle ⟨helement.1.1, helement.1.2,
      hsecond.1.fixed_le member hmember hmemberNe ⟨helement.1.1, helement.2⟩⟩
  have hpgroup : IsPGroup prime actor := IsPGroup.of_card hcard
  obtain ⟨firstSylow, hfirstSylowLe, hfirstSylowNormalized⟩ :=
    exists_normalized_sylow_containing_normalized_pSubgroup prime hprime subgroupPrime hsubgroupPrime
      actor overgroup firstPart hpgroup hovergroupCompatible.primeComplement hovergroupNormalized
        inf_le_right hfirstPartPGroup hfirstPartNormalized
  obtain ⟨secondSylow, hsecondSylowLe, hsecondSylowNormalized⟩ :=
    exists_normalized_sylow_containing_normalized_pSubgroup prime hprime subgroupPrime hsubgroupPrime
      actor overgroup secondPart hpgroup hovergroupCompatible.primeComplement hovergroupNormalized
        inf_le_right hsecondPartPGroup hsecondPartNormalized
  obtain ⟨conjugator, hconjugator, hconjugate⟩ :=
    exists_centralizing_conjugator_of_normalized_sylows prime hprime subgroupPrime hsubgroupPrime
      actor overgroup hpgroup hovergroupCompatible.primeComplement hovergroupNormalized
        firstSylow secondSylow hfirstSylowNormalized hsecondSylowNormalized
  have hconjugatorCommon : conjugator ∈ signalizerCommonFixed actor signalizer := by
    rw [signalizerCommonFixed_eq_value_centralizer prime actor actor signalizer hsignalizer
      le_rfl member hmember hmemberNe]
    exact ⟨hconjugator.1.2, hconjugator.2⟩
  have hlowerFixed : lower.map (MulAut.conj conjugator).toMonoidHom = lower :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hconjugator.1.1
  let productPart := (secondSylow : Subgroup overgroup).map overgroup.subtype
  have hproductPartLe : productPart ≤ overgroup := Subgroup.map_subtype_le _
  have hproductPartCompatible : SignalizerPrimeCompatible prime subgroupPrime actor signalizer productPart :=
    ⟨SignalizerCompatible.of_le prime actor signalizer overgroup productPart hovergroupCompatible
      hproductPartLe hsecondSylowNormalized, secondSylow.isPGroup'.map overgroup.subtype⟩
  have hproductPartNormalizes : productPart ≤ Subgroup.normalizer (lower : Set G) :=
    hproductPartLe.trans inf_le_left
  have hproductCompatible := SignalizerPrimeCompatible.normalized_sup prime hprime subgroupPrime
    actor signalizer hpgroup lower productPart hlowerCompatible hproductPartCompatible hproductPartNormalizes
  obtain ⟨maximal, hproductLe, hmaximal⟩ := exists_maximal_signalizer_prime_compatible_above
    prime subgroupPrime actor signalizer (lower ⊔ productPart) hproductCompatible
  have hlowerMaximal : lower ≤ maximal := le_sup_left.trans hproductLe
  have hproductPartMaximal : productPart ≤ maximal := le_sup_right.trans hproductLe
  have hlowerFirstConjugate : lower ≤ first.map (MulAut.conj conjugator).toMonoidHom := by
    rw [← hlowerFixed]
    exact Subgroup.map_mono inf_le_left
  have hfirstPartConjugateLe : firstPart.map (MulAut.conj conjugator).toMonoidHom ≤ productPart := by
    have hmapped := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hfirstSylowLe
    rw [hconjugate] at hmapped
    exact hmapped
  have hfirstPartConjugateNotLe : ¬firstPart.map (MulAut.conj conjugator).toMonoidHom ≤ lower := by
    intro hle
    apply hfirstNotLe
    have hmapped := Subgroup.map_mono (f := (MulAut.conj conjugator⁻¹).toMonoidHom) hle
    rw [subgroup_map_conj_inv_cancel] at hmapped
    have hlowerInverseFixed : lower.map (MulAut.conj conjugator⁻¹).toMonoidHom = lower := by
      calc
        lower.map (MulAut.conj conjugator⁻¹).toMonoidHom =
            (lower.map (MulAut.conj conjugator).toMonoidHom).map
              (MulAut.conj conjugator⁻¹).toMonoidHom := congrArg _ hlowerFixed.symm
        _ = lower := subgroup_map_conj_inv_cancel lower conjugator
    rw [hlowerInverseFixed] at hmapped
    exact hmapped
  refine ⟨conjugator, hconjugatorCommon, maximal, hmaximal, ?_, ?_⟩
  · apply lt_of_le_of_ne (le_inf hlowerFirstConjugate hlowerMaximal)
    intro heq
    apply hfirstPartConjugateNotLe
    rw [heq]
    exact le_inf (Subgroup.map_mono inf_le_left)
      (hfirstPartConjugateLe.trans hproductPartMaximal)
  · apply lt_of_le_of_ne (le_inf inf_le_right hlowerMaximal)
    intro heq
    apply hsecondNotLe
    change secondPart ≤ first ⊓ second
    rw [heq]
    exact le_inf inf_le_left (hsecondSylowLe.trans hproductPartMaximal)

end CFSG.RankThreeEvenClassification.Helpers
