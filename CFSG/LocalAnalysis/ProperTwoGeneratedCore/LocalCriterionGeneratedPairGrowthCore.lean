module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSetCore
public import CFSG.GroupTheory.PCore.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.SignalizerFunctor.Helpers

@[expose] def generatedPairGrowthPrimes (p : ℕ) : Set ℕ :=
  {r | r.Prime ∧ r ≠ 2 ∧ r ≠ p}

theorem generatedPairGrowth_prime_supported_iff {p m : ℕ} (hp : p.Prime) :
    primeSupported (generatedPairGrowthPrimes p) m ↔ Odd m ∧ Nat.Coprime p m := by
  constructor
  · intro hs
    refine ⟨?_, hp.coprime_iff_not_dvd.mpr (fun hd => (hs p hp hd).2.2 rfl)⟩
    apply Nat.odd_iff.mpr
    have hnot : ¬ 2 ∣ m := fun hd => (hs 2 Nat.prime_two hd).2.1 rfl
    have hmod : m % 2 ≠ 0 := fun he => hnot (Nat.dvd_of_mod_eq_zero he)
    omega
  · rintro ⟨hodd, hcoprime⟩ r hr hd
    refine ⟨hr, ?_, ?_⟩
    · intro he
      subst r
      have hzero := Nat.mod_eq_zero_of_dvd hd
      have hone := Nat.odd_iff.mp hodd
      omega
    · intro he
      subst r
      exact (hp.coprime_iff_not_dvd.mp hcoprime) hd

theorem generatedPairGrowth_prime_set_core_eq_pPrimeCore_oddCore
    (X : Type*) [Group X] [Finite X] {p : ℕ} (hp : p.Prime) :
    primeSetCore (GroupType := X) (generatedPairGrowthPrimes p) =
      (pPrimeCore p (CFSG.oddCore X)).map (CFSG.oddCore X).subtype := by
  let O := CFSG.oddCore X
  let C : Subgroup X := primeSetCore (generatedPairGrowthPrimes p)
  let : Fact p.Prime := ⟨hp⟩
  let : O.Characteristic := CFSG.ComponentClassification.OddCore.characteristic X
  let : C.Normal := prime_set_core_normal (generatedPairGrowthPrimes p)
  have hs : Odd (Nat.card C) ∧ Nat.Coprime p (Nat.card C) :=
    (generatedPairGrowth_prime_supported_iff hp).mp
      (prime_set_core_supported (generatedPairGrowthPrimes p))
  have hCO : C ≤ O := CFSG.ComponentClassification.OddCore.maximal X C inferInstance hs.1
  apply le_antisymm
  · have hc : Nat.Coprime p (Nat.card (C.subgroupOf O)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCO).toEquiv]
      exact hs.2
    have hsub : C.subgroupOf O ≤ pPrimeCore p O := le_sSup ⟨inferInstance, hc⟩
    have hmap := Subgroup.map_mono (f := O.subtype) hsub
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCO] at hmap
  · apply prime_set_core_contains
    · infer_instance
    · apply (generatedPairGrowth_prime_supported_iff hp).mpr
      refine ⟨?_, ?_⟩
      · exact (CFSG.ComponentClassification.OddCore.odd_card X).of_dvd_nat
          (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le (pPrimeCore p O)))
      · rw [Subgroup.card_subtype]
        exact pPrimeCore_coprime_card

theorem generatedPairGrowth_ambient_prime_set_core_eq
    {G : Type*} [Group G] [Finite G] (X : Subgroup G) {p : ℕ} (hp : p.Prime) :
    (primeSetCore (GroupType := X) (generatedPairGrowthPrimes p)).map X.subtype =
      (pPrimeCore p ((CFSG.oddCore X).map X.subtype)).map
        ((CFSG.oddCore X).map X.subtype).subtype := by
  let O := CFSG.oddCore X
  let J := O.map X.subtype
  let e : O ≃* J := O.equivMapOfInjective X.subtype X.subtype_injective
  have he : J.subtype.comp e.toMonoidHom = X.subtype.comp O.subtype := by
    ext a
    rfl
  rw [generatedPairGrowth_prime_set_core_eq_pPrimeCore_oddCore X hp, Subgroup.map_map]
  change (pPrimeCore p O).map (X.subtype.comp O.subtype) = (pPrimeCore p J).map J.subtype
  rw [← pPrimeCore_map_iso (p := p) (f := e), Subgroup.map_map, he]

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
