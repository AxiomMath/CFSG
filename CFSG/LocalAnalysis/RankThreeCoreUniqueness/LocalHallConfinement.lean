module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NormalizerClosure
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ElementaryCoordinates
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeSylowTransitivity

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal)
    (hquotient : IsPGroup prime (G ⧸ normalGroup)) (sylowGroup : Sylow prime G) :
    (sylowGroup : Subgroup G) ⊔ normalGroup = ⊤ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : normalGroup.Normal := hnormal
  let quotientSylow := sylowGroup.mapSurjective (QuotientGroup.mk'_surjective normalGroup)
  have hquotientTop : (quotientSylow : Subgroup (G ⧸ normalGroup)) = ⊤ := by
    exact (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hmap : (sylowGroup : Subgroup G).map (QuotientGroup.mk' normalGroup) = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact hquotientTop
  have hcomap := congrArg (fun subgroup : Subgroup (G ⧸ normalGroup) =>
    subgroup.comap (QuotientGroup.mk' normalGroup)) hmap
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap

theorem rank_three_hall_overgroup_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup localGroup hallGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup))
    (hhall : hallGroup ≤ localGroup)
    (hnormal : (hallGroup.subgroupOf localGroup).Normal)
    (hcoprime : prime.Coprime (Nat.card hallGroup))
    (hquotient : IsPGroup prime (localGroup ⧸ hallGroup.subgroupOf localGroup)) :
    localGroup ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : (hallGroup.subgroupOf localGroup).Normal := hnormal
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime
    (localGroup ⊓ overgroup) (by omega)
  have helementaryGroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  have helementaryRank : 3 ≤ pRank prime elementary := by
    unfold pRank
    exact hrank.trans (le_csSup (pRank_set_bddAbove prime hprime.one_lt elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩)
  have hhallNormalizer : localGroup ≤ Subgroup.normalizer (hallGroup : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hhall).mp hnormal
  have hhallLe := rank_three_signalizer_le_overgroup prime hprime sylowGroup overgroup
    elementary hallGroup hsylow hcore (hinclusion.trans inf_le_right) helementaryGroup
    helementaryRank ((hinclusion.trans inf_le_left).trans hhallNormalizer) hcoprime
  have helementaryInternal : IsPGroup prime (elementary.subgroupOf localGroup) :=
    helementaryGroup.of_equiv (Subgroup.subgroupOfEquivOfLe
      (hinclusion.trans inf_le_left)).symm
  obtain ⟨internalSylow, hinternalLe⟩ := helementaryInternal.exists_le_sylow
  let liftedSylow := (internalSylow : Subgroup localGroup).map localGroup.subtype
  have hsubgroupLe : elementary ≤ liftedSylow := by
    have himage := Subgroup.map_mono (f := localGroup.subtype) hinternalLe
    rwa [Subgroup.map_subgroupOf_eq_of_le (hinclusion.trans inf_le_left)] at himage
  have hliftedRank : 3 ≤ pRank prime (liftedSylow ⊓ overgroup) :=
    helementaryRank.trans (pRank_mono prime hprime.one_lt
      (le_inf hsubgroupLe (hinclusion.trans inf_le_right)))
  have hliftedLe := aschCore_two_pGroup_le_of_rank_three_intersection prime hprime sylowGroup
    overgroup hsylow hcore liftedSylow (internalSylow.isPGroup'.map _) hliftedRank
  have hsup := normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient prime hprime
    (hallGroup.subgroupOf localGroup) hnormal hquotient internalSylow
  have himage := congrArg (fun subgroup : Subgroup localGroup => subgroup.map localGroup.subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hhall] at himage
  have hmapTop : (⊤ : Subgroup localGroup).map localGroup.subtype = localGroup := by
    apply le_antisymm
    · rintro element ⟨preimage, _, rfl⟩
      exact preimage.property
    · intro element helement
      exact ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
  rw [hmapTop] at himage
  rw [← himage]
  exact sup_le hliftedLe hhallLe

theorem escaping_rank_three_overgroup_has_no_normal_hall_prime_complement
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup localGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    ∀ hallGroup : Subgroup G, hallGroup ≤ localGroup →
      ∀ _hnormal : (hallGroup.subgroupOf localGroup).Normal,
      prime.Coprime (Nat.card hallGroup) →
      ¬ IsPGroup prime (localGroup ⧸ hallGroup.subgroupOf localGroup) := by
  intro hallGroup hhall hnormal hcoprime hquotient
  exact hescape (rank_three_hall_overgroup_le prime hprime sylowGroup overgroup localGroup
    hallGroup hsylow hcore hrank hhall hnormal hcoprime hquotient)

theorem rank_three_overgroup_le_of_coprime_other_sylow_counts
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup localGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup))
    (hcounts : ∀ otherPrime : ℕ, otherPrime.Prime → otherPrime ≠ prime →
      ¬ prime ∣ Nat.card (Sylow otherPrime localGroup)) : localGroup ≤ overgroup := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨elementary, hinclusion, helementary, hcard⟩ := pRank_attained prime
    (localGroup ⊓ overgroup) (by omega)
  have helementaryGroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  have helementaryRank : 3 ≤ pRank prime elementary := by
    unfold pRank
    exact hrank.trans (le_csSup (pRank_set_bddAbove prime hprime.one_lt elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩)
  have helementaryLocal : elementary ≤ localGroup := hinclusion.trans inf_le_left
  have hnormalizing : elementary ≤ Subgroup.normalizer (localGroup : Set G) :=
    helementaryLocal.trans Subgroup.le_normalizer
  let action := ambientSubgroupActionHom elementary localGroup hnormalizing
  let : MulDistribMulAction elementary localGroup := multiplicativeActionOfMulAutHom action
  have hallSylows : ∀ otherPrime : ℕ, otherPrime.Prime →
      ∃ internalSylow : Sylow otherPrime localGroup,
        (internalSylow : Subgroup localGroup).map localGroup.subtype ≤ overgroup := by
    intro otherPrime hotherPrime
    let : Fact otherPrime.Prime := ⟨hotherPrime⟩
    by_cases hequal : otherPrime = prime
    · subst otherPrime
      have hinternalGroup : IsPGroup prime (elementary.subgroupOf localGroup) :=
        helementaryGroup.of_equiv (Subgroup.subgroupOfEquivOfLe helementaryLocal).symm
      obtain ⟨internalSylow, hinternalLe⟩ := hinternalGroup.exists_le_sylow
      let liftedSylow := (internalSylow : Subgroup localGroup).map localGroup.subtype
      have helementaryLe : elementary ≤ liftedSylow := by
        have himage := Subgroup.map_mono (f := localGroup.subtype) hinternalLe
        rwa [Subgroup.map_subgroupOf_eq_of_le helementaryLocal] at himage
      refine ⟨internalSylow, ?_⟩
      apply aschCore_two_pGroup_le_of_rank_three_intersection prime hprime sylowGroup
        overgroup hsylow hcore liftedSylow (internalSylow.isPGroup'.map localGroup.subtype)
      exact helementaryRank.trans (pRank_mono prime hprime.one_lt
        (le_inf helementaryLe (hinclusion.trans inf_le_right)))
    · let : MulAction elementary (Sylow otherPrime localGroup) := Sylow.pointwiseMulAction
      obtain ⟨internalSylow, hfixed⟩ :=
        helementaryGroup.nonempty_fixed_point_of_prime_not_dvd_card (Sylow otherPrime localGroup)
          (hcounts otherPrime hotherPrime hequal)
      have hfixedSubgroup : ∀ actingElement : elementary,
          (internalSylow : Subgroup localGroup).map (action actingElement).toMonoidHom =
            (internalSylow : Subgroup localGroup) := by
        intro actingElement
        have hequalSubgroup := congrArg (fun subgroup : Sylow otherPrime localGroup =>
          (subgroup : Subgroup localGroup)) (hfixed actingElement)
        rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hequalSubgroup
        exact hequalSubgroup
      let liftedSylow := (internalSylow : Subgroup localGroup).map localGroup.subtype
      have hliftedInvariant : elementary ≤ Subgroup.normalizer (liftedSylow : Set G) :=
        (ambient_subgroup_action_image_invariant_iff elementary localGroup hnormalizing
          (internalSylow : Subgroup localGroup)).mp hfixedSubgroup
      have hliftedPGroup : IsPGroup otherPrime liftedSylow := internalSylow.isPGroup'.map _
      have hliftedCoprime : prime.Coprime (Nat.card liftedSylow) := by
        obtain ⟨exponent, hcardinality⟩ := IsPGroup.iff_card.mp hliftedPGroup
        rw [hcardinality]
        exact (Nat.coprime_primes hprime hotherPrime |>.mpr (Ne.symm hequal)).pow_right exponent
      exact ⟨internalSylow, rank_three_signalizer_le_overgroup prime hprime sylowGroup
        overgroup elementary liftedSylow hsylow hcore (hinclusion.trans inf_le_right)
        helementaryGroup helementaryRank hliftedInvariant hliftedCoprime⟩
  have hcardDvd : Nat.card localGroup ∣ Nat.card ↥(localGroup ⊓ overgroup : Subgroup G) := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro otherPrime exponent hotherPrime hpowerDvd
    let : Fact otherPrime.Prime := ⟨hotherPrime⟩
    obtain ⟨internalSylow, hliftedLe⟩ := hallSylows otherPrime hotherPrime
    have hinternalDivisibility := internalSylow.pow_dvd_card_of_pow_dvd_card hpowerDvd
    have hcardMap := Nat.card_congr
      ((internalSylow : Subgroup localGroup).equivMapOfInjective localGroup.subtype
        localGroup.subtype_injective).toEquiv
    have hdivisibility : otherPrime ^ exponent ∣
        Nat.card ((internalSylow : Subgroup localGroup).map localGroup.subtype) := by
      rwa [← hcardMap]
    exact hdivisibility.trans (Subgroup.card_dvd_of_le (le_inf
      ((Subgroup.map_le_range _ _).trans localGroup.subtype_range.le) hliftedLe))
  have hinternalCard : Nat.card ((localGroup ⊓ overgroup).subgroupOf localGroup) =
      Nat.card localGroup := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show localGroup ⊓ overgroup ≤ localGroup from inf_le_left)).toEquiv]
    exact Nat.dvd_antisymm (Subgroup.card_dvd_of_le inf_le_left) hcardDvd
  have htop := ((localGroup ⊓ overgroup).subgroupOf localGroup).card_eq_iff_eq_top.mp hinternalCard
  exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right

theorem escaping_rank_three_overgroup_has_prime_divisible_other_sylow_count
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup localGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) (hescape : ¬ localGroup ≤ overgroup) :
    ∃ otherPrime : ℕ, otherPrime.Prime ∧ otherPrime ≠ prime ∧
      prime ∣ Nat.card (Sylow otherPrime localGroup) := by
  classical
  by_contra hnone
  push Not at hnone
  exact hescape (rank_three_overgroup_le_of_coprime_other_sylow_counts prime hprime sylowGroup
    overgroup localGroup hsylow hcore hrank hnone)

theorem sylow_invariant_coprime_signalizer_join_le_overgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (sylowGroup : Sylow prime G) (overgroup actingGroup : Subgroup G)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (sylowGroup : Subgroup G))
    (hsylowNormalizing : (sylowGroup : Subgroup G) ≤ Subgroup.normalizer (actingGroup : Set G))
    (hcoprime : prime.Coprime (Nat.card (rankTwoSignalizerJoin prime actingGroup))) :
    rankTwoSignalizerJoin prime actingGroup ≤ overgroup := by
  exact rank_three_signalizer_le_aschCore prime hprime (sylowGroup : Subgroup G)
    (sylowGroup : Subgroup G) (rankTwoSignalizerJoin prime actingGroup) le_rfl hrank
    (hsylowNormalizing.trans (normalizer_le_normalizer_rankTwoSignalizerJoin prime actingGroup))
    hcoprime |>.trans hcore

theorem full_sylow_escaping_normalizer_signalizer_join_has_prime_divisor
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (maximalLocal actingGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal maximalLocal) (hacting : actingGroup ≤ maximalLocal)
    (hsylow : (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ maximalLocal)
    (hrank : 3 ≤ pRank prime (sylowGroup : Subgroup G))
    (hsylowNormalizing : (sylowGroup : Subgroup G) ≤ Subgroup.normalizer (actingGroup : Set G))
    (hlocalConfinement : ∀ localGroup : Subgroup G, IsTwoLocal localGroup →
      3 ≤ pRank prime (localGroup ⊓ maximalLocal) → localGroup ≤ maximalLocal)
    (hescape : ¬ Subgroup.normalizer (actingGroup : Set G) ≤ maximalLocal) :
    prime ∣ Nat.card (rankTwoSignalizerJoin prime actingGroup) := by
  by_contra hnotDvd
  have hjoin := sylow_invariant_coprime_signalizer_join_le_overgroup prime hprime sylowGroup
    maximalLocal actingGroup hcore hrank hsylowNormalizing
    (hprime.coprime_iff_not_dvd.mpr hnotDvd)
  exact hescape (rankTwo_full_sylow_normalizer_signalizer_branch prime hprime hodd sylowGroup
    maximalLocal actingGroup hmaximal hacting hsylowNormalizing hsylow hrank
    ((rankTwoSignalizerJoin_le_iff prime actingGroup maximalLocal).mp hjoin) hlocalConfinement)

theorem maximal_invariant_two_subgroup_contains_local_twoCore
    {G : Type*} [Group G] [Finite G] (actingGroup localGroup twoGroup : Subgroup G)
    (hacting : actingGroup ≤ localGroup) (hcontained : twoGroup ≤ localGroup)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup) :
    pCoreOf 2 localGroup ≤ twoGroup := by
  have hjoinPGroup : IsPGroup 2 ↥(twoGroup ⊔ pCoreOf 2 localGroup : Subgroup G) :=
    hmaximal.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 localGroup)
      (hcontained.trans (localGroup_le_normalizer_pCoreOf 2 localGroup))
  have hjoinInvariant : actingGroup ≤
      Subgroup.normalizer ((twoGroup ⊔ pCoreOf 2 localGroup : Subgroup G) : Set G) :=
    (le_inf hmaximal.2.1 (hacting.trans (localGroup_le_normalizer_pCoreOf 2 localGroup))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup twoGroup (pCoreOf 2 localGroup))
  have hjoin := hmaximal.2.2 _ hjoinPGroup hjoinInvariant le_sup_left
  exact hjoin ▸ le_sup_right

theorem rank_three_maximal_invariant_two_subgroup_contains_overgroup_twoCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (overgroup actingGroup twoGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hacting : actingGroup ≤ overgroup) (hactor : IsPGroup prime actingGroup)
    (hrank : 3 ≤ pRank prime actingGroup)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup) :
    twoGroup ≤ overgroup ∧ pCoreOf 2 overgroup ≤ twoGroup := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hmaximal.1
  have hcoprime : prime.Coprime (Nat.card twoGroup) := by
    rw [hcard]
    exact (Nat.coprime_primes hprime Nat.prime_two |>.mpr hodd).pow_right exponent
  have hcontained := rank_three_signalizer_le_overgroup prime hprime sylowGroup overgroup
    actingGroup twoGroup hsylow hcore hacting hactor hrank hmaximal.2.1 hcoprime
  exact ⟨hcontained, maximal_invariant_two_subgroup_contains_local_twoCore actingGroup
    overgroup twoGroup hacting hcontained hmaximal⟩

theorem rank_three_intersection_local_twoCores_have_invariant_twoGroup_join
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (sylowGroup : Sylow prime G) (overgroup localGroup : Subgroup G)
    (hsylow : (sylowGroup : Subgroup G) ≤ overgroup)
    (hcore : rankThreeAschCore 2 prime (sylowGroup : Subgroup G) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup)) :
    IsPGroup 2 ↥(pCoreOf 2 overgroup ⊔ pCoreOf 2 localGroup : Subgroup G) ∧
      (pCoreOf 2 overgroup ⊔ pCoreOf 2 localGroup : Subgroup G) ≤ overgroup ∧
      localGroup ⊓ overgroup ≤ Subgroup.normalizer
        ((pCoreOf 2 overgroup ⊔ pCoreOf 2 localGroup : Subgroup G) : Set G) := by
  have hlocalCore := two_local_rank_three_intersection_twoCore_le_overgroup prime hprime hodd
    sylowGroup overgroup localGroup hsylow hcore hrank
  refine ⟨(pCoreOf_isPGroup 2 overgroup).to_sup_of_normal_left'
    (pCoreOf_isPGroup 2 localGroup)
    (hlocalCore.trans (localGroup_le_normalizer_pCoreOf 2 overgroup)),
    sup_le (pCoreOf_le 2 overgroup) hlocalCore, ?_⟩
  exact (le_inf (inf_le_right.trans (localGroup_le_normalizer_pCoreOf 2 overgroup))
    (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 localGroup))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (pCoreOf 2 overgroup)
      (pCoreOf 2 localGroup))

theorem exists_maximal_invariant_two_subgroup_containing
    {G : Type*} [Group G] [Finite G] (actingGroup twoGroup : Subgroup G)
    (htwoGroup : IsPGroup 2 twoGroup)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (twoGroup : Set G)) :
    ∃ maximalGroup : Subgroup G, twoGroup ≤ maximalGroup ∧
      rankTwoMaximalInvariantTwoSubgroup actingGroup maximalGroup := by
  obtain ⟨maximalGroup, hinclusion, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => IsPGroup 2 subgroup ∧
      actingGroup ≤ Subgroup.normalizer (subgroup : Set G)) ⟨htwoGroup, hinvariant⟩
  exact ⟨maximalGroup, hinclusion, hmaximal.1.1, hmaximal.1.2,
    fun larger hgroup hnormalized hcontained => le_antisymm
      (hmaximal.2 ⟨hgroup, hnormalized⟩ hcontained) hcontained⟩

end CFSG.RankThreeCoreUniqueness.Helpers
