module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSpectrum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerTransitivity

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem exists_plane_in_rank_three_actor {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G)
    (hpower : ∀ member : actor, member ^ prime = 1) (hcard : Nat.card actor = prime ^ 3) :
    ∃ plane : Subgroup G, plane ≤ actor ∧ Nat.card plane = prime ^ 2 ∧
      ∀ member : plane, member ^ prime = 1 := by
  have hlarge : prime ^ 2 ≤ Nat.card actor := by
    rw [hcard, pow_succ]
    exact Nat.le_mul_of_pos_right _ hprime.pos
  obtain ⟨internalPlane, hinternalCard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card hprime (IsPGroup.of_card hcard) hlarge
  let plane := internalPlane.map actor.subtype
  have hplaneLe : plane ≤ actor := Subgroup.map_subtype_le _
  refine ⟨plane, hplaneLe,
    (Subgroup.card_map_of_injective actor.subtype_injective).trans hinternalCard, ?_⟩
  intro member
  apply Subtype.ext
  exact congrArg (fun value : actor => (value : G)) (hpower ⟨member, hplaneLe member.property⟩)

theorem SignalizerCompatible.isPGroup_of_spectrum_subset_singleton
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ)
    (actor plane : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hplaneLe : plane ≤ actor)
    (hpower : ∀ member : plane, member ^ prime = 1) (hplaneCard : Nat.card plane = prime ^ 2)
    (hspectrum : signalizerSpectrum actor signalizer ⊆ {subgroupPrime})
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup) :
    IsPGroup subgroupPrime subgroup := by
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro divisor hdivisor hdiv
  exact Set.mem_singleton_iff.mp (hspectrum
    (SignalizerCompatible.prime_dvd_mem_spectrum prime hprime actor plane signalizer hpgroup
      hplaneLe hpower hplaneCard subgroup hcompatible divisor hdivisor hdiv))

theorem signalizer_complete_of_spectrum_subset_singleton
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ) (hsubgroupPrime : subgroupPrime.Prime)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3)
    (hspectrum : signalizerSpectrum actor signalizer ⊆ {subgroupPrime}) :
    SignalizerComplete prime actor signalizer := by
  obtain ⟨plane, hplaneLe, hplaneCard, hplanePower⟩ :=
    exists_plane_in_rank_three_actor prime hprime actor hpower hcard
  have hpgroup : IsPGroup prime actor := IsPGroup.of_card hcard
  have hallPrimeCompatible : ∀ subgroup : Subgroup G,
      SignalizerCompatible prime actor signalizer subgroup →
        SignalizerPrimeCompatible prime subgroupPrime actor signalizer subgroup := by
    intro subgroup hcompatible
    exact ⟨hcompatible,
      SignalizerCompatible.isPGroup_of_spectrum_subset_singleton prime hprime subgroupPrime
        actor plane signalizer hpgroup hplaneLe hplanePower hplaneCard hspectrum subgroup hcompatible⟩
  have hactorNe : actor ≠ ⊥ := by
    intro heq
    have hone := Subgroup.card_eq_one.mpr heq
    rw [hcard] at hone
    have hlarge : 1 < prime ^ 3 := by nlinarith [hprime.two_le]
    omega
  obtain ⟨member, hmemberNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hactorNe
  have hmemberAmbientNe : (member : G) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
  have hcommonCompatible := signalizerCommonFixed_compatible prime hprime actor actor signalizer
    hsignalizer le_rfl member member.property hmemberAmbientNe
  obtain ⟨greatest, hcommonLe, hgreatest⟩ := exists_maximal_signalizer_prime_compatible_above
    prime subgroupPrime actor signalizer (signalizerCommonFixed actor signalizer)
      (hallPrimeCompatible _ hcommonCompatible)
  apply (signalizer_complete_iff_exists_greatest_compatible prime hprime actor plane signalizer
    hsignalizer hplaneLe hplanePower hplaneCard).mpr
  refine ⟨greatest, hgreatest.1.1, ?_⟩
  intro subgroup hcompatible
  obtain ⟨maximal, hsubgroupLe, hmaximal⟩ := exists_maximal_signalizer_prime_compatible_above
    prime subgroupPrime actor signalizer subgroup (hallPrimeCompatible subgroup hcompatible)
  obtain ⟨conjugator, hconjugator, hconjugate⟩ := signalizer_prime_compatible_transitivity
    prime hprime subgroupPrime hsubgroupPrime actor signalizer hsignalizer hcomm hpower hcard
      greatest maximal hgreatest hmaximal
  have hfixed : greatest.map (MulAut.conj conjugator).toMonoidHom = greatest :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hcommonLe hconjugator))
  rw [hfixed] at hconjugate
  exact hconjugate.symm ▸ hsubgroupLe

theorem signalizer_complete_of_spectrum_subsingleton
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3)
    (hspectrum : (signalizerSpectrum actor signalizer).Subsingleton) :
    SignalizerComplete prime actor signalizer := by
  rcases hspectrum.eq_empty_or_singleton with hempty | ⟨subgroupPrime, hsingleton⟩
  · exact signalizer_complete_of_spectrum_empty prime hprime actor signalizer hempty
  · have hmem : subgroupPrime ∈ signalizerSpectrum actor signalizer := by
      rw [hsingleton]
      exact Set.mem_singleton subgroupPrime
    exact signalizer_complete_of_spectrum_subset_singleton prime hprime subgroupPrime hmem.1
      actor signalizer hsignalizer hcomm hpower hcard (hsingleton ▸ Set.Subset.refl _)

end CFSG.RankThreeEvenClassification.Helpers
