module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSpectrum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeValues

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem abelian_actor_le_element_centralizer {G : Type u} [Group G]
    (actor : Subgroup G) (hcomm : IsMulCommutative actor) (element : G) (hmem : element ∈ actor) :
    actor ≤ Subgroup.centralizer ({element} : Set G) :=
  (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans
    (centralizer_actor_le_element_centralizer actor element hmem)

theorem primeSetSignalizer_fixed_candidate {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomm : IsMulCommutative actor)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (first second : G) (hfirst : first ∈ actor) (hfirstNe : first ≠ 1)
    (hsecond : second ∈ actor) (hsecondNe : second ≠ 1) :
    SignalizerPrimeValueCandidate primes actor signalizer second
      (primeSetSignalizer primes actor signalizer first ⊓ Subgroup.centralizer {second}) := by
  have hfirstCandidate :=
    primeSetSignalizer_candidate prime hprime primes actor signalizer hpgroup hsignalizer first hfirst hfirstNe
  refine ⟨(inf_le_inf hfirstCandidate.1 le_rfl).trans
    (hsignalizer.balance first hfirst hfirstNe second hsecond hsecondNe), ?_, ?_, ?_⟩
  · exact normalizes_inf_of_normalizes_both actor _ _ hfirstCandidate.2.1
      ((abelian_actor_le_element_centralizer actor hcomm second hsecond).trans Subgroup.le_normalizer)
  · exact PrimeSetOrder.of_dvd primes _ _ hfirstCandidate.2.2.1
      (Subgroup.card_dvd_of_le inf_le_left)
  · exact normalizes_inf_of_normalizes_both (signalizerCommonFixed actor signalizer) _ _
      hfirstCandidate.2.2.2
      (((signalizerCommonFixed_le_centralizer prime actor actor signalizer hsignalizer le_rfl).trans
        (centralizer_actor_le_element_centralizer actor second hsecond)).trans Subgroup.le_normalizer)

theorem primeSetSignalizer_isSolvableSignalizerFunctor {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomm : IsMulCommutative actor)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    IsSolvableSignalizerFunctor prime actor (primeSetSignalizer primes actor signalizer) := by
  constructor
  · intro element hmem hne
    exact (primeSetSignalizer_le_value primes actor signalizer element).trans
      (hsignalizer.le_centralizer element hmem hne)
  · intro element hmem hne
    exact (hsignalizer.coprime element hmem hne).of_dvd_right
      (Subgroup.card_dvd_of_le (primeSetSignalizer_le_value primes actor signalizer element))
  · intro element hmem hne member hmember
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (primeSetSignalizer_normalized prime hprime primes actor signalizer hpgroup hsignalizer element hmem hne hmember)
  · intro first hfirst hfirstNe second hsecond hsecondNe
    exact le_primeSetSignalizer_of_candidate primes actor signalizer second _
      (primeSetSignalizer_fixed_candidate prime hprime primes actor signalizer hpgroup hcomm hsignalizer
        first second hfirst hfirstNe hsecond hsecondNe)
  · intro element hmem hne
    have : Group.IsSolvable (signalizer element) := hsignalizer.solvable element hmem hne
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (primeSetSignalizer_le_value primes actor signalizer element))
      (Subgroup.inclusion_injective _)

theorem signalizerSpectrum_primeSetSignalizer_subset {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer) :
    signalizerSpectrum actor (primeSetSignalizer primes actor signalizer) ⊆
      primes ∩ signalizerSpectrum actor signalizer := by
  intro divisor hdivisor
  obtain ⟨hdivisorPrime, element, hmem, hne, hdiv⟩ := hdivisor
  exact ⟨primeSetSignalizer_primeSetOrder prime hprime primes actor signalizer hpgroup hsignalizer
    element hmem hne divisor hdivisorPrime hdiv,
    hdivisorPrime, element, hmem, hne,
    hdiv.trans (Subgroup.card_dvd_of_le (primeSetSignalizer_le_value primes actor signalizer element))⟩

theorem SignalizerCompatible.primeSetSignalizer_of_fixed_normalized {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (primes : Set ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hcomm : IsMulCommutative actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (subgroup : Subgroup G) (hcompatible : SignalizerCompatible prime actor signalizer subgroup)
    (horder : PrimeSetOrder primes (Nat.card subgroup))
    (hnormalized : signalizerCommonFixed actor signalizer ≤ Subgroup.normalizer (subgroup : Set G)) :
    SignalizerCompatible prime actor (primeSetSignalizer primes actor signalizer) subgroup := by
  refine ⟨hcompatible.normalized, hcompatible.solvable, hcompatible.primeComplement, ?_⟩
  intro element hmem hne
  apply le_primeSetSignalizer_of_candidate
  refine ⟨hcompatible.fixed_le element hmem hne, ?_, ?_, ?_⟩
  · exact normalizes_inf_of_normalizes_both actor _ _ hcompatible.normalized
      ((abelian_actor_le_element_centralizer actor hcomm element hmem).trans Subgroup.le_normalizer)
  · exact PrimeSetOrder.of_dvd primes _ _ horder (Subgroup.card_dvd_of_le inf_le_left)
  · exact normalizes_inf_of_normalizes_both (signalizerCommonFixed actor signalizer) _ _ hnormalized
      (((signalizerCommonFixed_le_centralizer prime actor actor signalizer hsignalizer le_rfl).trans
        (centralizer_actor_le_element_centralizer actor element hmem)).trans Subgroup.le_normalizer)

end CFSG.RankThreeEvenClassification.Helpers
