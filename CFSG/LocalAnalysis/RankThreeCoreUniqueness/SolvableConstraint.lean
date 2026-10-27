module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem coprime_comap_of_coprime_kernel
    {G : Type*} [Group G] [Finite G] {Q : Type*} [Group Q]
    (prime : ℕ) (homomorphism : G →* Q) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (subgroup : Subgroup Q) (hcoprime : prime.Coprime (Nat.card subgroup)) :
    prime.Coprime (Nat.card (Subgroup.comap homomorphism subgroup)) := by
  have hcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) homomorphism.ker
    (Subgroup.comap homomorphism subgroup) bot_le (Subgroup.ker_le_comap _ _)
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.relIndex_ker,
    Subgroup.map_comap_eq_self_of_surjective hsurjective] at hcard
  rw [← hcard]
  exact hkernel.mul_right hcoprime

theorem primeComplementCore_quotient_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    primeComplementCore (G := G ⧸ primeComplementCore prime) prime = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  rintro subgroup ⟨hnormal, hcoprime⟩
  let homomorphism := QuotientGroup.mk' (primeComplementCore (G := G) prime)
  have hkernel : prime.Coprime (Nat.card homomorphism.ker) := by
    dsimp only [homomorphism]
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime prime
  have hbound : Subgroup.comap homomorphism subgroup ≤ primeComplementCore prime :=
    normal_coprime_le_primeComplementCore prime _ (hnormal.comap homomorphism)
      (coprime_comap_of_coprime_kernel prime homomorphism
        (QuotientGroup.mk'_surjective _) hkernel subgroup hcoprime)
  intro element helement
  obtain ⟨representative, hrepresentative⟩ := QuotientGroup.mk'_surjective
    (primeComplementCore (G := G) prime) element
  have hpreimage : representative ∈ Subgroup.comap homomorphism subgroup := by
    change homomorphism representative ∈ subgroup
    rwa [hrepresentative]
  apply Subgroup.mem_bot.mpr
  rw [← hrepresentative]
  exact (QuotientGroup.eq_one_iff representative).mpr (hbound hpreimage)

theorem normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore (G := G) prime = ⊥)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal)
    (hnilpotent : Group.IsNilpotent normalGroup) : IsPGroup prime normalGroup := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : normalGroup.Normal := hnormal
  let : Group.IsNilpotent normalGroup := hnilpotent
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne')
  intro otherPrime hotherPrime hdivides
  by_contra hdistinct
  let : Fact otherPrime.Prime := ⟨hotherPrime⟩
  let sylowGroup : Sylow otherPrime normalGroup := Classical.choice inferInstance
  have hsylowNormal : (sylowGroup : Subgroup normalGroup).Normal :=
    sylowGroup.normal_of_normalizerCondition
      (Group.normalizerCondition_of_isNilpotent (G := normalGroup))
  let : (sylowGroup : Subgroup normalGroup).Characteristic :=
    sylowGroup.characteristic_of_normal hsylowNormal
  have hambientNormal : (Subgroup.map normalGroup.subtype
      (sylowGroup : Subgroup normalGroup)).Normal := by infer_instance
  have hcoprime : prime.Coprime (Nat.card (sylowGroup : Subgroup normalGroup)) := by
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp sylowGroup.isPGroup'
    rw [hcard]
    exact ((Nat.coprime_primes hprime hotherPrime).mpr (Ne.symm hdistinct)).pow_right exponent
  have hambientBot : Subgroup.map normalGroup.subtype
      (sylowGroup : Subgroup normalGroup) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact normal_coprime_le_primeComplementCore prime _ hambientNormal
      (hcoprime.of_dvd_right
        ((sylowGroup : Subgroup normalGroup).card_map_dvd normalGroup.subtype))
  have hsylowBot : (sylowGroup : Subgroup normalGroup) = ⊥ := by
    have hcomap := congrArg (Subgroup.comap normalGroup.subtype) hambientBot
    rw [Subgroup.comap_map_eq_self_of_injective normalGroup.subtype_injective] at hcomap
    change (sylowGroup : Subgroup normalGroup) = normalGroup.subtype.ker at hcomap
    rwa [normalGroup.ker_subtype] at hcomap
  exact sylowGroup.ne_bot_of_dvd_card hdivides hsylowBot

theorem centralizer_normal_of_normal
    {G : Type*} [Group G] (normalGroup : Subgroup G) (hnormal : normalGroup.Normal) :
    (Subgroup.centralizer (normalGroup : Set G)).Normal := by
  let : normalGroup.Normal := hnormal
  have hinternal := Subgroup.normal_subgroupOf_centralizer_normalizer (normalGroup : Set G)
  rw [Subgroup.normalizer_eq_top] at hinternal
  apply Subgroup.normalizer_eq_top_iff.mp
  exact top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hinternal)

theorem solvable_centralizer_pCore_le_of_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore (G := G) prime = ⊥)
    (hsolvable : Group.IsSolvable (Subgroup.centralizer (pCore prime G : Set G))) :
    Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G := by
  let centralizingGroup := Subgroup.centralizer (pCore prime G : Set G)
  let : Group.IsSolvable centralizingGroup := hsolvable
  let : centralizingGroup.Normal := centralizer_normal_of_normal _ (pCore_normal prime)
  obtain ⟨derivedLength, hderived⟩ := Group.IsSolvable.solvable (G := centralizingGroup)
  have hdescending : ∀ index, Subgroup.map centralizingGroup.subtype
      (derivedSeries centralizingGroup index) ≤ pCore prime G := by
    have hstep (index : ℕ)
        (hnext : Subgroup.map centralizingGroup.subtype
          (derivedSeries centralizingGroup (index + 1)) ≤ pCore prime G) :
        Subgroup.map centralizingGroup.subtype
          (derivedSeries centralizingGroup index) ≤ pCore prime G := by
      let derivedGroup := Subgroup.map centralizingGroup.subtype
        (derivedSeries centralizingGroup index)
      have hnormal : derivedGroup.Normal := by infer_instance
      have hcommutator : ⁅derivedGroup, derivedGroup⁆ ≤ pCore prime G := by
        simpa only [derivedGroup, derivedSeries_succ, Subgroup.map_commutator] using hnext
      have hcentralizes : derivedGroup ≤ Subgroup.centralizer (pCore prime G : Set G) :=
        (Subgroup.map_subtype_le _)
      have hnilpotent : Group.IsNilpotent derivedGroup := by
        apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 2)
        rw [show 2 = 1 + 1 by rfl, Subgroup.lowerCentralSeries_succ,
          Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
        apply le_bot_iff.mp
        have hzero : ⁅pCore prime G, derivedGroup⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralizes
        exact (Subgroup.commutator_mono hcommutator le_rfl).trans (le_of_eq hzero)
      exact normal_pGroup_le_pCore prime derivedGroup hnormal
        (normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot
          prime hprime hcore derivedGroup hnormal hnilpotent)
    intro index
    by_cases hlarge : derivedLength ≤ index
    · have hzero := derivedSeries_antitone centralizingGroup hlarge
      rw [hderived] at hzero
      rw [le_bot_iff.mp hzero, Subgroup.map_bot]
      exact bot_le
    · have hdown : ∀ offset, Subgroup.map centralizingGroup.subtype
          (derivedSeries centralizingGroup (derivedLength - offset)) ≤ pCore prime G := by
        intro offset
        induction offset with
        | zero => simpa only [Nat.sub_zero, hderived, Subgroup.map_bot] using
            (bot_le : (⊥ : Subgroup G) ≤ pCore prime G)
        | succ offset inductionHypothesis =>
          by_cases hbound : offset < derivedLength
          · have hindex : derivedLength - (offset + 1) + 1 = derivedLength - offset := by omega
            apply hstep
            rwa [hindex]
          · have hindex : derivedLength - (offset + 1) = derivedLength - offset := by omega
            rwa [hindex]
      have hindex : derivedLength - (derivedLength - index) = index := by omega
      simpa only [hindex] using hdown (derivedLength - index)
  have hzero := hdescending 0
  simpa only [derivedSeries_zero, ← MonoidHom.range_eq_map,
    centralizingGroup.subtype_range] using hzero

theorem solvable_hasPrimeConstraint
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) : HasPrimeConstraint (G := G) prime := by
  refine ⟨pCore prime (G ⧸ primeComplementCore prime), pCore_normal prime,
    pCore_isPGroup prime, ?_⟩
  exact solvable_centralizer_pCore_le_of_primeComplementCore_eq_bot prime hprime
    (primeComplementCore_quotient_eq_bot prime) inferInstance

theorem hasPrimeConstraint_iff_pCore_centralizer_le
    {G : Type*} [Group G] (prime : ℕ) :
    HasPrimeConstraint (G := G) prime ↔
      Subgroup.centralizer (pCore prime (G ⧸ primeComplementCore prime) : Set _) ≤
        pCore prime (G ⧸ primeComplementCore prime) := by
  constructor
  · rintro ⟨normalGroup, hnormal, hgroup, hcentralizer⟩
    have hbound := normal_pGroup_le_pCore prime normalGroup hnormal hgroup
    exact (Subgroup.centralizer_le hbound).trans (hcentralizer.trans hbound)
  · intro hcentralizer
    exact ⟨pCore prime (G ⧸ primeComplementCore prime), pCore_normal prime,
      pCore_isPGroup prime, hcentralizer⟩

theorem not_prime_constrained_has_nonsolvable_core_centralizer
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    ¬ Group.IsSolvable
      (Subgroup.centralizer (pCore prime (G ⧸ primeComplementCore prime) :
        Set (G ⧸ primeComplementCore prime))) := by
  intro hsolvable
  apply hconstraint
  apply (hasPrimeConstraint_iff_pCore_centralizer_le prime).mpr
  exact solvable_centralizer_pCore_le_of_primeComplementCore_eq_bot prime hprime
    (primeComplementCore_quotient_eq_bot prime) hsolvable

theorem solvable_signalizer_le_primeComplementCore
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup signalizer : Subgroup G) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    signalizer ≤ primeComplementCore prime :=
  prime_constraint_signalizer_le_primeComplementCore prime hprime hodd
    (solvable_hasPrimeConstraint prime hprime) actingGroup signalizer hactor hsignalizer
    hinvariant hcontains

theorem rank_two_maximal_pair_transitive_of_solvable_overgroup
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup first second overgroup : Subgroup G) [Group.IsSolvable overgroup]
    (hactor : IsPGroup prime actingGroup) (hactorLe : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hcontains : ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) :
    ∃ conjugator : G, conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second :=
  rank_two_maximal_pair_transitive_of_prime_constraint prime hprime hodd
    actingGroup first second overgroup hactor hactorLe hfirst hsecond hfirstLe hsecondLe
    (solvable_hasPrimeConstraint prime hprime) hcontains

theorem rank_two_nontransitive_pair_overgroup_not_solvable
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (actingGroup first second overgroup : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hactorLe : actingGroup ≤ overgroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hcontains : ∀ element : G, element ∈ overgroup →
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup)
    (hnontransitive : ¬ ∃ conjugator : G,
      conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second) :
    ¬ Group.IsSolvable overgroup := by
  intro hsolvable
  let : Group.IsSolvable overgroup := hsolvable
  exact hnontransitive (rank_two_maximal_pair_transitive_of_solvable_overgroup
    prime hprime hodd actingGroup first second overgroup hactor hactorLe hfirst hsecond
    hfirstLe hsecondLe hcontains)

end CFSG.RankThreeCoreUniqueness.Helpers
