module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.AmbientHallIntersection

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def SignalizerPrimeValueCandidate {G : Type u} [Group G]
    (primes : Set ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (subgroup : Subgroup G) : Prop :=
  subgroup ≤ signalizer element ∧ actor ≤ Subgroup.normalizer (subgroup : Set G) ∧
    PrimeSetOrder primes (Nat.card subgroup) ∧
    signalizerCommonFixed actor signalizer ≤ Subgroup.normalizer (subgroup : Set G)

@[expose] noncomputable def primeSetSignalizer {G : Type u} [Group G]
    (primes : Set ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G) (element : G) : Subgroup G :=
  ⨆ subgroup : {candidate : Subgroup G // SignalizerPrimeValueCandidate primes actor signalizer element candidate},
    subgroup.val

theorem primeSetSignalizer_le_value {G : Type u} [Group G]
    (primes : Set ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G) (element : G) :
    primeSetSignalizer primes actor signalizer element ≤ signalizer element := by
  apply iSup_le
  intro subgroup
  exact subgroup.property.1

theorem le_primeSetSignalizer_of_candidate {G : Type u} [Group G]
    (primes : Set ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (element : G) (subgroup : Subgroup G)
    (hcandidate : SignalizerPrimeValueCandidate primes actor signalizer element subgroup) :
    subgroup ≤ primeSetSignalizer primes actor signalizer element := by
  unfold primeSetSignalizer
  exact le_iSup (fun candidate : {candidate : Subgroup G //
    SignalizerPrimeValueCandidate primes actor signalizer element candidate} => candidate.val)
    ⟨subgroup, hcandidate⟩

theorem primeSetSignalizer_candidate {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    SignalizerPrimeValueCandidate primes actor signalizer element
      (primeSetSignalizer primes actor signalizer element) := by
  have hvalue := signalizer_value_compatible prime hprime actor signalizer hsignalizer element hmem hne
  obtain ⟨greatest, hle, hnormalized, horder, hfixedNormalized, hgreatest⟩ :=
    exists_greatest_fixed_normalized_primeSetSubgroup prime hprime actor (signalizer element)
      hpgroup hvalue.normalized hvalue.solvable hvalue.primeComplement primes
  have hfixedEq : signalizerCommonFixed actor signalizer =
      signalizer element ⊓ Subgroup.centralizer (actor : Set G) :=
    signalizerCommonFixed_eq_value_centralizer prime actor actor signalizer hsignalizer le_rfl element hmem hne
  have hcandidate : SignalizerPrimeValueCandidate primes actor signalizer element greatest :=
    ⟨hle, hnormalized, horder, hfixedEq.symm ▸ hfixedNormalized⟩
  have heq : primeSetSignalizer primes actor signalizer element = greatest := by
    apply le_antisymm
    · apply iSup_le
      intro candidate
      exact hgreatest candidate.val candidate.property.1 candidate.property.2.1
        candidate.property.2.2.1 (hfixedEq ▸ candidate.property.2.2.2)
    · exact le_primeSetSignalizer_of_candidate primes actor signalizer element greatest hcandidate
  rw [heq]
  exact hcandidate

theorem primeSetSignalizer_primeSetOrder {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    PrimeSetOrder primes (Nat.card (primeSetSignalizer primes actor signalizer element)) :=
  (primeSetSignalizer_candidate prime hprime primes actor signalizer hpgroup hsignalizer element hmem hne).2.2.1

theorem primeSetSignalizer_normalized {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    actor ≤ Subgroup.normalizer (primeSetSignalizer primes actor signalizer element : Set G) :=
  (primeSetSignalizer_candidate prime hprime primes actor signalizer hpgroup hsignalizer element hmem hne).2.1

theorem primeSetSignalizer_common_fixed_normalized {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (primes : Set ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G)
    (hpgroup : IsPGroup prime actor) (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    signalizerCommonFixed actor signalizer ≤
      Subgroup.normalizer (primeSetSignalizer primes actor signalizer element : Set G) :=
  (primeSetSignalizer_candidate prime hprime primes actor signalizer hpgroup hsignalizer element hmem hne).2.2.2

end CFSG.RankThreeEvenClassification.Helpers
