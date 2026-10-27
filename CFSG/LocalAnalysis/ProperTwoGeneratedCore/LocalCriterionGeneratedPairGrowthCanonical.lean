module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthCore

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.SignalizerFunctor.Helpers

@[expose] def generatedPairGrowthCanonicalPrimes (p : ℕ) : Set Nat.Primes :=
  {r | r.val ≠ 2 ∧ r.val ≠ p}

theorem generatedPairGrowth_prime_set_core_eq_piCore
    {G : Type*} [Group G] (primes : Set ℕ) :
    primeSetCore (GroupType := G) primes = piCore {r : Nat.Primes | r.val ∈ primes} G := by
  apply le_antisymm
  · unfold primeSetCore
    apply iSup_le
    intro N
    apply iSup_le
    rintro ⟨hnormal, hsupported⟩
    apply le_sSup
    refine ⟨hnormal, ?_⟩
    intro r hr
    exact hsupported r.val r.property hr
  · unfold piCore
    apply sSup_le
    rintro N ⟨hnormal, hsupported⟩
    apply prime_set_core_contains primes N hnormal
    intro r hr hrdvd
    exact hsupported (⟨r, hr⟩ : Nat.Primes) hrdvd

theorem generatedPairGrowth_literal_core_eq_canonical
    {G : Type*} [Group G] (p : ℕ) :
    primeSetCore (GroupType := G) (generatedPairGrowthPrimes p) =
      piCore (generatedPairGrowthCanonicalPrimes p) G := by
  rw [generatedPairGrowth_prime_set_core_eq_piCore]
  congr 1
  ext r
  constructor
  · exact fun hr => hr.2
  · exact fun hr => ⟨r.property, hr⟩

theorem generatedPairGrowth_canonical_core_eq_pPrimeCore_oddCore
    (G : Type*) [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    piCore (generatedPairGrowthCanonicalPrimes p) G =
      (pPrimeCore p (CFSG.oddCore G)).map (CFSG.oddCore G).subtype := by
  rw [← generatedPairGrowth_literal_core_eq_canonical]
  exact generatedPairGrowth_prime_set_core_eq_pPrimeCore_oddCore G hp

theorem generatedPairGrowth_ambient_canonical_core_eq
    {G : Type*} [Group G] [Finite G] (X : Subgroup G) {p : ℕ} (hp : p.Prime) :
    (piCore (generatedPairGrowthCanonicalPrimes p) X).map X.subtype =
      (pPrimeCore p ((CFSG.oddCore X).map X.subtype)).map
        ((CFSG.oddCore X).map X.subtype).subtype := by
  rw [← generatedPairGrowth_literal_core_eq_canonical]
  exact generatedPairGrowth_ambient_prime_set_core_eq X hp

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
