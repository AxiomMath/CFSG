module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedCentralizerObstruction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem finite_perfectResidual_eq_bot_iff_solvable
    {G : Type*} [Group G] [Finite G] :
    perfectResidual G = ⊥ ↔ Group.IsSolvable G := by
  constructor
  · intro hbottom
    obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
    exact ⟨index, hindex.symm.trans hbottom⟩
  · rintro ⟨index, hindex⟩
    exact le_bot_iff.mp ((iInf_le _ index).trans hindex.le)

theorem finite_perfectResidual_map_eq
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Finite Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    Subgroup.map homomorphism (perfectResidual G) = perfectResidual Image := by
  apply le_antisymm
  · apply le_iInf
    intro index
    exact (Subgroup.map_mono (iInf_le _ index)).trans
      (map_derivedSeries_le_derivedSeries homomorphism index)
  · obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
    have hbound := derivedSeries_le_map_derivedSeries hsurjective index
    rw [← hindex] at hbound
    exact (iInf_le _ index).trans hbound

theorem perfect_subgroup_le_perfectResidual
    {G : Type*} [Group G] (perfectGroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup) : perfectGroup ≤ perfectResidual G := by
  apply le_iInf
  intro index
  induction index with
  | zero => exact le_top
  | succ index hinduction =>
    rw [derivedSeries_succ, ← Subgroup.isPerfect_iff.mp hperfect]
    exact Subgroup.commutator_mono hinduction hinduction

theorem perfect_subgroup_le_perfectResidualOf
    {G : Type*} [Group G] (perfectGroup overgroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup) (hcontained : perfectGroup ≤ overgroup) :
    perfectGroup ≤ perfectResidualOf overgroup := by
  have hinternal : Group.IsPerfect (perfectGroup.subgroupOf overgroup) := by
    apply Subgroup.isPerfect_iff.mpr
    have hmap := Subgroup.map_commutator (perfectGroup.subgroupOf overgroup)
      (perfectGroup.subgroupOf overgroup) overgroup.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hcontained, Subgroup.isPerfect_iff.mp hperfect] at hmap
    apply (Subgroup.map_injective overgroup.subtype_injective)
    exact hmap.trans (Subgroup.map_subgroupOf_eq_of_le hcontained).symm
  have hbound := Subgroup.map_mono (f := overgroup.subtype)
    (perfect_subgroup_le_perfectResidual (perfectGroup.subgroupOf overgroup) hinternal)
  rwa [Subgroup.map_subgroupOf_eq_of_le hcontained] at hbound

@[expose] def reducedCoreCentralizer (G : Type*) [Group G] (prime : ℕ) :
    Subgroup (G ⧸ primeComplementCore prime) :=
  Subgroup.centralizer (pCore prime (G ⧸ primeComplementCore prime) : Set _)

theorem reducedCoreCentralizer_characteristic
    {G : Type*} [Group G] (prime : ℕ) :
    (reducedCoreCentralizer G prime).Characteristic := by
  let : (pCore prime (G ⧸ primeComplementCore prime)).Characteristic :=
    pCore_characteristic prime
  unfold reducedCoreCentralizer
  infer_instance

@[expose] def reducedPerfectObstruction (G : Type*) [Group G] (prime : ℕ) :
    Subgroup (G ⧸ primeComplementCore prime) :=
  perfectResidualOf (reducedCoreCentralizer G prime)

theorem reducedPerfectObstruction_characteristic
    {G : Type*} [Group G] (prime : ℕ) :
    (reducedPerfectObstruction G prime).Characteristic := by
  let : (reducedCoreCentralizer G prime).Characteristic :=
    reducedCoreCentralizer_characteristic prime
  let : (perfectResidual (reducedCoreCentralizer G prime)).Characteristic :=
    perfectResidual_characteristic
  unfold reducedPerfectObstruction perfectResidualOf
  infer_instance

theorem reducedPerfectObstruction_isPerfect
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    Group.IsPerfect (reducedPerfectObstruction G prime) :=
  finite_perfectResidualOf_isPerfect _

theorem reducedPerfectObstruction_le_coreCentralizer
    {G : Type*} [Group G] (prime : ℕ) :
    reducedPerfectObstruction G prime ≤ reducedCoreCentralizer G prime :=
  Subgroup.map_subtype_le _

theorem non_prime_constrained_reducedPerfectObstruction_ne_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    reducedPerfectObstruction G prime ≠ ⊥ := by
  have hnonsolvable := not_prime_constrained_has_nonsolvable_core_centralizer
    prime hprime hconstraint
  have hinternal : perfectResidual (reducedCoreCentralizer G prime) ≠ ⊥ :=
    fun hbottom => hnonsolvable (finite_perfectResidual_eq_bot_iff_solvable.mp hbottom)
  exact ((Subgroup.map_eq_bot_iff_of_injective _
    (reducedCoreCentralizer G prime).subtype_injective).not).mpr hinternal

theorem reducedPerfectObstruction_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    primeComplementCore (G := reducedPerfectObstruction G prime) prime = ⊥ := by
  let : (reducedPerfectObstruction G prime).Characteristic :=
    reducedPerfectObstruction_characteristic prime
  have hbound := normal_subgroup_primeComplementCore_le prime
    (reducedPerfectObstruction G prime) inferInstance
  rw [primeComplementCore_quotient_eq_bot] at hbound
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (reducedPerfectObstruction G prime).subtype_injective).mp (le_bot_iff.mp hbound)

theorem reducedPerfectObstruction_contains_perfect_coreCentralizer_subgroups
    {G : Type*} [Group G] (prime : ℕ)
    (perfectGroup : Subgroup (G ⧸ primeComplementCore prime))
    (hperfect : Group.IsPerfect perfectGroup)
    (hcentralizes : perfectGroup ≤ reducedCoreCentralizer G prime) :
    perfectGroup ≤ reducedPerfectObstruction G prime :=
  perfect_subgroup_le_perfectResidualOf perfectGroup _ hperfect hcentralizes

theorem non_prime_constrained_reducedPerfectObstruction_prime_dvd_card
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    prime ∣ Nat.card (reducedPerfectObstruction G prime) := by
  by_contra hnotDivides
  let : (reducedPerfectObstruction G prime).Characteristic :=
    reducedPerfectObstruction_characteristic prime
  have hbound := normal_coprime_le_primeComplementCore prime
    (reducedPerfectObstruction G prime) inferInstance
    (hprime.coprime_iff_not_dvd.mpr hnotDivides)
  rw [primeComplementCore_quotient_eq_bot] at hbound
  exact non_prime_constrained_reducedPerfectObstruction_ne_bot prime hprime hconstraint
    (le_bot_iff.mp hbound)

@[expose] def canonicalLocalObstruction (G : Type*) [Group G] (prime : ℕ) : Subgroup G :=
  perfectResidualOf (Subgroup.comap (QuotientGroup.mk' (primeComplementCore prime))
    (reducedPerfectObstruction G prime))

theorem canonicalLocalObstruction_characteristic
    {G : Type*} [Group G] (prime : ℕ) :
    (canonicalLocalObstruction G prime).Characteristic := by
  let : (primeComplementCore (G := G) prime).Characteristic :=
    primeComplementCore_characteristic prime
  let preimageGroup := Subgroup.comap (QuotientGroup.mk' (primeComplementCore (G := G) prime))
    (reducedPerfectObstruction G prime)
  let : preimageGroup.Characteristic := Subgroup.Characteristic.comap_quotient_mk
    (reducedPerfectObstruction_characteristic prime)
  let : (perfectResidual preimageGroup).Characteristic := perfectResidual_characteristic
  unfold canonicalLocalObstruction perfectResidualOf
  change (Subgroup.map preimageGroup.subtype (perfectResidual preimageGroup)).Characteristic
  infer_instance

theorem canonicalLocalObstruction_isPerfect
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    Group.IsPerfect (canonicalLocalObstruction G prime) :=
  finite_perfectResidualOf_isPerfect _

theorem canonicalLocalObstruction_image_eq
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    Subgroup.map (QuotientGroup.mk' (primeComplementCore prime))
      (canonicalLocalObstruction G prime) = reducedPerfectObstruction G prime :=
  finite_canonical_perfect_preimage_image_eq _ (QuotientGroup.mk'_surjective _) _
    (reducedPerfectObstruction_isPerfect prime)

theorem non_prime_constrained_canonicalLocalObstruction_ne_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    canonicalLocalObstruction G prime ≠ ⊥ := by
  intro hbottom
  have himage := canonicalLocalObstruction_image_eq (G := G) prime
  rw [hbottom, Subgroup.map_bot] at himage
  exact non_prime_constrained_reducedPerfectObstruction_ne_bot prime hprime hconstraint
    himage.symm

theorem canonicalLocalObstruction_quotient_equiv
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    Nonempty ((canonicalLocalObstruction G prime ⧸ primeComplementCore prime) ≃*
      reducedPerfectObstruction G prime) := by
  apply finite_canonical_coprime_perfect_preimage_quotient_equiv prime _
    (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime prime
  · exact reducedPerfectObstruction_isPerfect prime
  · exact reducedPerfectObstruction_primeComplementCore_eq_bot prime

theorem canonicalLocalObstruction_contains_perfect_lifts
    {G : Type*} [Group G] (prime : ℕ) (perfectGroup : Subgroup G)
    (hperfect : Group.IsPerfect perfectGroup)
    (himage : Subgroup.map (QuotientGroup.mk' (primeComplementCore prime)) perfectGroup ≤
      reducedPerfectObstruction G prime) :
    perfectGroup ≤ canonicalLocalObstruction G prime :=
  perfect_subgroup_le_perfectResidualOf perfectGroup _ hperfect
    (Subgroup.map_le_iff_le_comap.mp himage)

theorem canonicalLocalObstructionOf_normalizer_contains
    {G : Type*} [Group G] (prime : ℕ) (overgroup : Subgroup G) :
    Subgroup.normalizer (overgroup : Set G) ≤ Subgroup.normalizer
      (Subgroup.map overgroup.subtype (canonicalLocalObstruction overgroup prime) : Set G) :=
  normalizer_le_normalizer_characteristic_map overgroup _
    (canonicalLocalObstruction_characteristic prime)

theorem canonicalLocalObstructionOf_twoCore_normalizer_contains
    {G : Type*} [Group G] (prime : ℕ) (overgroup : Subgroup G) :
    Subgroup.normalizer (overgroup : Set G) ≤ Subgroup.normalizer
      (Subgroup.map overgroup.subtype
        (pCoreOf 2 (canonicalLocalObstruction overgroup prime)) : Set G) := by
  let : (canonicalLocalObstruction overgroup prime).Characteristic :=
    canonicalLocalObstruction_characteristic prime
  let : (pCore 2 (canonicalLocalObstruction overgroup prime)).Characteristic :=
    pCore_characteristic 2
  apply normalizer_le_normalizer_characteristic_map overgroup
  change (Subgroup.map (canonicalLocalObstruction overgroup prime).subtype
    (pCore 2 (canonicalLocalObstruction overgroup prime))).Characteristic
  infer_instance

theorem non_prime_constrained_canonicalLocalObstruction_prime_dvd_card
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    prime ∣ Nat.card (canonicalLocalObstruction G prime) := by
  have hdivides := non_prime_constrained_reducedPerfectObstruction_prime_dvd_card
    prime hprime hconstraint
  rw [← canonicalLocalObstruction_image_eq prime] at hdivides
  exact hdivides.trans ((canonicalLocalObstruction G prime).card_map_dvd _)

end CFSG.RankThreeCoreUniqueness.Helpers
