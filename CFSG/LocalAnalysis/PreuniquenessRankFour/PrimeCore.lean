module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem normal_coprime_sup
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (first second : Subgroup source)
    [first.Normal] [second.Normal]
    (hfirst : ¬ prime ∣ Nat.card first) (hsecond : ¬ prime ∣ Nat.card second) :
    ¬ prime ∣ Nat.card (first ⊔ second : Subgroup source) := by
  let joinGroup := first ⊔ second
  let normal := second.subgroupOf joinGroup
  let : normal.Normal := inferInstance
  let equivalence := QuotientGroup.quotientInfEquivProdNormalQuotient first second
  have hquotient : ¬ prime ∣ Nat.card (joinGroup ⧸ normal) := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact fun hdivides => hfirst
      (hdivides.trans (Subgroup.card_quotient_dvd_card (second.subgroupOf first)))
  have hnormal : ¬ prime ∣ Nat.card normal := by
    rw [Nat.card_congr (second.subgroupOfEquivOfLe
      (show second ≤ joinGroup from le_sup_right)).toEquiv]
    exact hsecond
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup normal]
  exact fun hdivides => ((hprime.dvd_mul.mp hdivides).elim hquotient hnormal)

theorem exists_largest_normal_coprime_subgroup
    (source : Type u) [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) :
    ∃ largest : Subgroup source, largest.Normal ∧ ¬ prime ∣ Nat.card largest ∧
      ∀ candidate : Subgroup source, candidate.Normal →
        ¬ prime ∣ Nat.card candidate → candidate ≤ largest := by
  have hbot : (⊥ : Subgroup source).Normal ∧ ¬ prime ∣ Nat.card (⊥ : Subgroup source) := by
    exact ⟨inferInstance, by simpa only [Subgroup.card_bot] using hprime.not_dvd_one⟩
  obtain ⟨largest, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun candidate : Subgroup source => candidate.Normal ∧ ¬ prime ∣ Nat.card candidate)
    (a := ⊥) hbot
  let : largest.Normal := hmaximal.1.1
  refine ⟨largest, hmaximal.1.1, hmaximal.1.2, ?_⟩
  intro candidate hnormal hcoprime
  let : candidate.Normal := hnormal
  have hjoin : (largest ⊔ candidate : Subgroup source).Normal ∧
      ¬ prime ∣ Nat.card (largest ⊔ candidate : Subgroup source) :=
    ⟨inferInstance, normal_coprime_sup prime hprime largest candidate hmaximal.1.2 hcoprime⟩
  have hequal : largest ⊔ candidate = largest :=
    le_antisymm (hmaximal.2 hjoin le_sup_left) le_sup_left
  exact hequal ▸ le_sup_right

theorem primeCore_eq_largest_normal_coprime_image
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient) :
    ∃ largest : Subgroup source, largest.Normal ∧ ¬ prime ∣ Nat.card largest ∧
      GLBPrimeCore prime source = largest.map source.subtype := by
  obtain ⟨largest, hnormal, hcoprime, hlargest⟩ :=
    exists_largest_normal_coprime_subgroup source prime hprime
  let : largest.Normal := hnormal
  refine ⟨largest, hnormal, hcoprime, le_antisymm ?_ ?_⟩
  · apply sSup_le
    rintro candidate ⟨hcontained, hcandidateNormal, hcandidateCoprime⟩
    have hcoprimeLocal : ¬ prime ∣ Nat.card (candidate.subgroupOf source) := by
      rw [Nat.card_congr (candidate.subgroupOfEquivOfLe hcontained).toEquiv]
      exact (hprime.coprime_iff_not_dvd.mp hcandidateCoprime)
    rw [← Subgroup.map_subgroupOf_eq_of_le hcontained]
    exact Subgroup.map_mono (hlargest _ hcandidateNormal hcoprimeLocal)
  · apply le_sSup
    refine ⟨Subgroup.map_subtype_le largest, ?_, ?_⟩
    · rw [show (largest.map source.subtype).subgroupOf source = largest from
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective largest]
      infer_instance
    · rw [Subgroup.card_map_of_injective Subtype.val_injective]
      exact hprime.coprime_iff_not_dvd.mpr hcoprime

theorem primeCore_le
    {ambient : Type u} [Group ambient] (prime : ℕ) (source : Subgroup ambient) :
    GLBPrimeCore prime source ≤ source := by
  apply sSup_le
  rintro candidate ⟨hcontained, _, _⟩
  exact hcontained

theorem primeCore_normal
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient) :
    ((GLBPrimeCore prime source).subgroupOf source).Normal := by
  obtain ⟨largest, hnormal, _, hequal⟩ :=
    primeCore_eq_largest_normal_coprime_image prime hprime source
  rw [hequal]
  rw [show (largest.map source.subtype).subgroupOf source = largest from
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective largest]
  exact hnormal

theorem primeCore_coprime
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient) :
    Nat.Coprime prime (Nat.card (GLBPrimeCore prime source)) := by
  obtain ⟨largest, _, hcoprime, hequal⟩ :=
    primeCore_eq_largest_normal_coprime_image prime hprime source
  rw [hequal, Subgroup.card_map_of_injective Subtype.val_injective]
  exact hprime.coprime_iff_not_dvd.mpr hcoprime

theorem primeCore_normalizer_normalizes
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient) :
    Subgroup.normalizer (source : Set ambient) ≤
      Subgroup.normalizer (GLBPrimeCore prime source : Set ambient) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator hconjugator member hmember
  let automorphism := source.normalizerMonoidHom ⟨conjugator, hconjugator⟩
  obtain ⟨largest, hnormal, hcoprime, hequal⟩ :=
    primeCore_eq_largest_normal_coprime_image prime hprime source
  rw [hequal] at hmember ⊢
  obtain ⟨lift, hlift, rfl⟩ := hmember
  have himageNormal := hnormal.map automorphism.toMonoidHom automorphism.surjective
  have himageCoprime : ¬ prime ∣ Nat.card (largest.map automorphism.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := automorphism.toMonoidHom) automorphism.injective]
    exact hcoprime
  have himageContained : largest.map automorphism.toMonoidHom ≤ largest := by
    have hcoreImage : (largest.map automorphism.toMonoidHom).map source.subtype ≤
        GLBPrimeCore prime source := by
      apply le_sSup
      refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
      · rw [show ((largest.map automorphism.toMonoidHom).map source.subtype).subgroupOf source =
          largest.map automorphism.toMonoidHom from
          Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _]
        exact himageNormal
      · rw [Subgroup.card_map_of_injective Subtype.val_injective]
        exact hprime.coprime_iff_not_dvd.mpr himageCoprime
    rw [hequal] at hcoreImage
    exact (Subgroup.map_le_map_iff_of_injective Subtype.val_injective).mp hcoreImage
  exact Subgroup.mem_map.mpr ⟨automorphism lift,
    himageContained (Subgroup.mem_map_of_mem _ hlift),
    source.normalizerMonoidHom_apply_apply_coe ⟨conjugator, hconjugator⟩ lift⟩

theorem normal_coprime_quotient_has_no_normal_coprime_subgroup
    (source : Type u) [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime)
    (largest : Subgroup source) [largest.Normal]
    (hcoprime : ¬ prime ∣ Nat.card largest)
    (hlargest : ∀ candidate : Subgroup source, candidate.Normal →
      ¬ prime ∣ Nat.card candidate → candidate ≤ largest)
    (normal : Subgroup (source ⧸ largest)) [normal.Normal]
    (hnormalCoprime : ¬ prime ∣ Nat.card normal) : normal = ⊥ := by
  let hom := QuotientGroup.mk' largest
  let lifted := normal.comap hom
  let : lifted.Normal := inferInstance
  have hlargestLift : largest ≤ lifted := by
    intro member hmember
    change hom member ∈ normal
    rw [show hom member = 1 from (QuotientGroup.eq_one_iff member).mpr hmember]
    exact normal.one_mem
  have hliftedCoprime : ¬ prime ∣ Nat.card lifted := by
    let restriction := hom.subgroupMap lifted
    have himage : lifted.map hom = normal :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective largest) normal
    have hkernel : restriction.ker = largest.subgroupOf lifted := by
      ext member
      change (⟨hom member, _⟩ : lifted.map hom) = 1 ↔ (member : source) ∈ largest
      rw [Subtype.ext_iff]
      exact @QuotientGroup.eq_one_iff source _ largest _ member
    have hkernelCard : Nat.card restriction.ker = Nat.card largest := by
      rw [hkernel, Nat.card_congr (largest.subgroupOfEquivOfLe hlargestLift).toEquiv]
    have hquotientCard : Nat.card (lifted ⧸ restriction.ker) = Nat.card normal := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective restriction
        (hom.subgroupMap_surjective lifted)).toEquiv, himage]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup restriction.ker,
      hquotientCard, hkernelCard]
    exact fun hdivides => (hprime.dvd_mul.mp hdivides).elim hnormalCoprime hcoprime
  have hequal : lifted = largest := le_antisymm (hlargest _ inferInstance hliftedCoprime) hlargestLift
  have himage : lifted.map hom = normal :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective largest) normal
  rw [hequal] at himage
  have hzero : largest.map hom = ⊥ := by
    exact (Subgroup.map_eq_bot_iff largest).mpr (by rw [QuotientGroup.ker_mk'])
  exact himage.symm.trans hzero

theorem normal_prime_section_le_of_rank_three_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary source normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    (hnormalSource : normal ≤ source) [(normal.subgroupOf source).Normal]
    (hnormalContained : normal ≤ overgroup)
    (hsourceNormalized : elementary ≤ Subgroup.normalizer (source : Set ambient))
    (hquotient : IsPGroup prime (source ⧸ normal.subgroupOf source)) :
    source ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨sourceSylow, hnormalized⟩ := exists_normalized_same_prime_sylow prime
    (IsPGroup.of_card hcard) hsourceNormalized
  let liftedSylow := (sourceSylow : Subgroup source).map source.subtype
  have hjoinGroup : IsPGroup prime (elementary ⊔ liftedSylow : Subgroup ambient) :=
    IsPGroup.to_sup_of_normal_right' (IsPGroup.of_card hcard)
      (sourceSylow.isPGroup'.map source.subtype) hnormalized
  have hjoinRank : 3 ≤ pRank prime
      ((elementary ⊔ liftedSylow : Subgroup ambient) ⊓ overgroup) := by
    exact hrank.trans (le_csSup (pRank_bddAbove prime hprime _)
      ⟨elementary, le_inf le_sup_left helementaryContained, helementary, hcard⟩)
  have hsylowContained : liftedSylow ≤ overgroup :=
    (show liftedSylow ≤ elementary ⊔ liftedSylow from le_sup_right).trans
      (intersecting_pSubgroup_le prime hprime sylow hsylow hcore hjoinGroup hjoinRank)
  let hom := QuotientGroup.mk' (normal.subgroupOf source)
  let quotientSylow := Sylow.mapSurjective
    (QuotientGroup.mk'_surjective (normal.subgroupOf source)) sourceSylow
  have himageTop : (sourceSylow : Subgroup source).map hom = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hgenerates : (sourceSylow : Subgroup source) ⊔ normal.subgroupOf source = ⊤ := by
    rw [← QuotientGroup.ker_mk' (normal.subgroupOf source),
      ← Subgroup.comap_map_eq, himageTop]
    exact Subgroup.comap_top _
  have hsourceMap : (⊤ : Subgroup source).map source.subtype ≤ overgroup := by
    rw [← hgenerates, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hnormalSource]
    exact sup_le hsylowContained hnormalContained
  intro member hmember
  exact hsourceMap (Subgroup.mem_map_of_mem source.subtype
    (Subgroup.mem_top (⟨member, hmember⟩ : source)))

theorem primeCore_quotient_has_no_normal_coprime_subgroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal]
    (hcoprime : ¬ prime ∣ Nat.card normal) : normal = ⊥ := by
  apply normal_coprime_quotient_has_no_normal_coprime_subgroup source prime hprime
    ((GLBPrimeCore prime source).subgroupOf source)
  · rw [Nat.card_congr ((GLBPrimeCore prime source).subgroupOfEquivOfLe
      (primeCore_le prime source)).toEquiv]
    exact hprime.coprime_iff_not_dvd.mp (primeCore_coprime prime hprime source)
  · intro candidate hnormal hcandidateCoprime
    have himage : candidate.map source.subtype ≤ GLBPrimeCore prime source := by
      apply le_sSup
      refine ⟨Subgroup.map_subtype_le candidate, ?_, ?_⟩
      · rw [show (candidate.map source.subtype).subgroupOf source = candidate from
          Subgroup.comap_map_eq_self_of_injective Subtype.val_injective candidate]
        exact hnormal
      · rw [Subgroup.card_map_of_injective Subtype.val_injective]
        exact hprime.coprime_iff_not_dvd.mpr hcandidateCoprime
    exact Subgroup.map_le_iff_le_comap.mp himage
  · exact hcoprime

theorem intersecting_rank_three_primeCore_quotient_normal_primeSubgroup_lift_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal]
    (hnormalGroup : IsPGroup prime normal) :
    (normal.comap (QuotientGroup.mk' ((GLBPrimeCore prime source).subgroupOf source))).map
      source.subtype ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  suffices hcontained :
      (normal.comap (QuotientGroup.mk' ((GLBPrimeCore prime source).subgroupOf source))).map
        source.subtype ≤ overgroup by exact hcontained
  · let radical := (GLBPrimeCore prime source).subgroupOf source
    let hom := QuotientGroup.mk' radical
    let lifted := normal.comap hom
    let liftedAmbient := lifted.map source.subtype
    let radicalAmbient := GLBPrimeCore prime source
    have hradicalContained : radicalAmbient ≤ overgroup :=
      intersecting_local_primeCore_le prime hprime sylow hsylow hcore hrank
    have hradicalLift : radical ≤ lifted := by
      intro member hmember
      change hom member ∈ normal
      rw [show hom member = 1 from (QuotientGroup.eq_one_iff member).mpr hmember]
      exact normal.one_mem
    have hradicalLiftAmbient : radicalAmbient ≤ liftedAmbient := by
      change GLBPrimeCore prime source ≤ lifted.map source.subtype
      rw [← Subgroup.map_subgroupOf_eq_of_le (primeCore_le prime source)]
      exact Subgroup.map_mono hradicalLift
    let : lifted.Normal := inferInstance
    let : (radicalAmbient.subgroupOf liftedAmbient).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hradicalLiftAmbient).mpr
      exact (Subgroup.map_subtype_le lifted).trans
        (Subgroup.le_normalizer.trans (primeCore_normalizer_normalizes prime hprime source))
    obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
      pRank_attained prime hprime (source ⊓ overgroup)
    have hliftedNormal : (liftedAmbient.subgroupOf source).Normal := by
      rw [show liftedAmbient.subgroupOf source = lifted from
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective lifted]
      infer_instance
    have hnormalized : elementary ≤ Subgroup.normalizer (liftedAmbient : Set ambient) :=
      (helementaryContained.trans inf_le_left).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.map_subtype_le lifted)).mp hliftedNormal)
    let equivalence : lifted ≃* liftedAmbient :=
      lifted.equivMapOfInjective source.subtype Subtype.val_injective
    let quotientRestriction := hom.subgroupMap lifted
    have himage : lifted.map hom = normal :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective radical) normal
    have hkernel : quotientRestriction.ker = radical.subgroupOf lifted := by
      ext member
      change (⟨hom member, _⟩ : lifted.map hom) = 1 ↔ (member : source) ∈ radical
      rw [Subtype.ext_iff]
      exact @QuotientGroup.eq_one_iff source _ radical _ member
    have hquotientGroup : IsPGroup prime (lifted ⧸ radical.subgroupOf lifted) := by
      have hgroup : IsPGroup prime (lifted.map hom) := himage.symm ▸ hnormalGroup
      have hquotient := hgroup.of_equiv (QuotientGroup.quotientKerEquivOfSurjective
        quotientRestriction (hom.subgroupMap_surjective lifted)).symm
      exact hquotient.of_equiv (QuotientGroup.congr quotientRestriction.ker
        (radical.subgroupOf lifted) (MulEquiv.refl lifted) (by simpa using hkernel))
    have hradicalImage : (radical.subgroupOf lifted).map equivalence.toMonoidHom =
        radicalAmbient.subgroupOf liftedAmbient := by
      ext member
      constructor
      · rintro ⟨lift, hlift, rfl⟩
        exact hlift
      · intro hmember
        obtain ⟨lift, rfl⟩ := equivalence.surjective member
        exact ⟨lift, hmember, rfl⟩
    have hquotientAmbientGroup : IsPGroup prime
        (liftedAmbient ⧸ radicalAmbient.subgroupOf liftedAmbient) :=
      hquotientGroup.of_equiv (QuotientGroup.congr (radical.subgroupOf lifted)
        (radicalAmbient.subgroupOf liftedAmbient) equivalence hradicalImage)
    have hcontained : liftedAmbient ≤ overgroup :=
      normal_prime_section_le_of_rank_three_elementary prime hprime sylow hsylow hcore
        helementary (pRank prime (source ⊓ overgroup)) hrank hcard
        (helementaryContained.trans inf_le_right) hradicalLiftAmbient hradicalContained
        hnormalized hquotientAmbientGroup
    exact hcontained

theorem pGroup_quotient_subgroupMap_injective_of_coprime_kernel
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (normal : Subgroup source) [normal.Normal]
    (hcoprime : ¬ prime ∣ Nat.card normal)
    (subgroup : Subgroup source) (hgroup : IsPGroup prime subgroup) :
    Function.Injective ((QuotientGroup.mk' normal).subgroupMap subgroup) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let hom := (QuotientGroup.mk' normal).subgroupMap subgroup
  apply hom.ker_eq_bot_iff.mp
  apply (Subgroup.eq_bot_iff_forall hom.ker).mpr
  intro member hmember
  have hnormalMember : (member : source) ∈ normal := by
    have hequal : (QuotientGroup.mk' normal) member = 1 := by
      exact congrArg Subtype.val hmember
    exact (@QuotientGroup.eq_one_iff source _ normal _ member).mp hequal
  have hinf : subgroup ⊓ normal = ⊥ := by
    obtain ⟨rank, hcard⟩ := IsPGroup.iff_card.mp hgroup
    apply (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hcard]
    exact (hprime.coprime_iff_not_dvd.mpr hcoprime).pow_left rank
  have hone : (member : source) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hinf]
    exact ⟨member.property, hnormalMember⟩
  exact Subtype.ext hone

theorem pRank_quotient_map_of_coprime_normal
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (normal : Subgroup source) [normal.Normal]
    (hcoprime : ¬ prime ∣ Nat.card normal) (subgroup : Subgroup source) :
    pRank prime (subgroup.map (QuotientGroup.mk' normal)) = pRank prime subgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let hom := QuotientGroup.mk' normal
  apply le_antisymm
  · obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
      pRank_attained prime hprime (subgroup.map hom)
    let restricted := hom.subgroupMap subgroup
    let elementaryLocal := elementary.subgroupOf (subgroup.map hom)
    have helementaryGroup : IsPGroup prime elementaryLocal :=
      (IsPGroup.of_card hcard).comap_subtype
    obtain ⟨quotientSylow, hquotientSylow⟩ := helementaryGroup.exists_le_sylow
    obtain ⟨sourceSylow, hsourceSylow⟩ :=
      Sylow.mapSurjective_surjective (hom.subgroupMap_surjective subgroup) prime quotientSylow
    let liftedSylow := (sourceSylow : Subgroup subgroup).map subgroup.subtype
    have hsylowGroup : IsPGroup prime liftedSylow := sourceSylow.isPGroup'.map subgroup.subtype
    let sylowHom := hom.subgroupMap liftedSylow
    have hsylowInjective : Function.Injective sylowHom :=
      pGroup_quotient_subgroupMap_injective_of_coprime_kernel prime hprime normal hcoprime
        liftedSylow hsylowGroup
    have helementaryImage : elementary ≤ liftedSylow.map hom := by
      rw [Subgroup.map_map]
      intro member hmember
      let localMember : subgroup.map hom := ⟨member, helementaryContained hmember⟩
      have hmemberSylow : localMember ∈ quotientSylow := hquotientSylow hmember
      rw [← hsourceSylow] at hmemberSylow
      change localMember ∈ ((Sylow.mapSurjective
        (hom.subgroupMap_surjective subgroup) sourceSylow) : Subgroup (subgroup.map hom))
        at hmemberSylow
      rw [Sylow.coe_mapSurjective] at hmemberSylow
      obtain ⟨lift, hlift, hequal⟩ := hmemberSylow
      exact ⟨lift, hlift, congrArg Subtype.val hequal⟩
    let imageElementary := elementary.subgroupOf (liftedSylow.map hom)
    let liftedElementary := imageElementary.comap sylowHom
    have hmap : liftedElementary.map sylowHom = imageElementary :=
      Subgroup.map_comap_eq_self_of_surjective (hom.subgroupMap_surjective liftedSylow) _
    have hliftedComm : IsMulCommutative liftedElementary := by
      let : IsMulCommutative elementary := helementary.1
      exact Subgroup.comap_injective_isMulCommutative imageElementary hsylowInjective
    have hliftedElementary : IsElemAbelian prime liftedElementary := by
      refine ⟨hliftedComm, ?_⟩
      intro member hmember
      apply hsylowInjective
      apply Subtype.ext
      change hom ((member : source) ^ prime) = hom 1
      have hmemberImage : hom member ∈ elementary := hmember
      rw [map_pow, helementary.2 _ hmemberImage, map_one]
    let ambientElementary := liftedElementary.map liftedSylow.subtype
    have hambientElementary : IsElemAbelian prime ambientElementary :=
      elementary_abelian_map prime hliftedElementary liftedSylow.subtype
    have hambientContained : ambientElementary ≤ subgroup :=
      (Subgroup.map_subtype_le liftedElementary).trans (Subgroup.map_subtype_le (sourceSylow : Subgroup subgroup))
    have hambientCard : Nat.card ambientElementary = prime ^
        pRank prime (subgroup.map hom) := by
      rw [Subgroup.card_map_of_injective (f := liftedSylow.subtype) Subtype.val_injective,
        ← Subgroup.card_map_of_injective (f := sylowHom) hsylowInjective, hmap,
        Nat.card_congr (elementary.subgroupOfEquivOfLe helementaryImage).toEquiv, hcard]
    exact le_csSup (pRank_bddAbove prime hprime subgroup)
      ⟨ambientElementary, hambientContained, hambientElementary, hambientCard⟩
  · obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
      pRank_attained prime hprime subgroup
    have hinjective := pGroup_quotient_subgroupMap_injective_of_coprime_kernel prime hprime
      normal hcoprime elementary (IsPGroup.of_card hcard)
    have hmapCard : Nat.card (elementary.map hom) = Nat.card elementary :=
      Nat.card_congr (MulEquiv.ofBijective (hom.subgroupMap elementary)
        ⟨hinjective, hom.subgroupMap_surjective elementary⟩).toEquiv.symm
    exact le_csSup (pRank_bddAbove prime hprime (subgroup.map hom))
      ⟨elementary.map hom, Subgroup.map_mono helementaryContained,
        elementary_abelian_map prime helementary hom, hmapCard.trans hcard⟩

theorem escaping_rank_three_primeCore_quotient_normal_primeSubgroup_rank_le_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormalGroup : IsPGroup prime normal) : pRank prime normal ≤ 2 := by
  let radical := (GLBPrimeCore prime source).subgroupOf source
  let hom := QuotientGroup.mk' radical
  let lifted := normal.comap hom
  let : lifted.Normal := inferInstance
  have hcontained : lifted.map source.subtype ≤ overgroup :=
    intersecting_rank_three_primeCore_quotient_normal_primeSubgroup_lift_le
      prime hprime sylow hsylow hcore hrank normal hnormalGroup
  have hcoprime : ¬ prime ∣ Nat.card radical := by
    rw [Nat.card_congr ((GLBPrimeCore prime source).subgroupOfEquivOfLe
      (primeCore_le prime source)).toEquiv]
    exact hprime.coprime_iff_not_dvd.mp (primeCore_coprime prime hprime source)
  have hrankEqual : pRank prime (lifted.map source.subtype) = pRank prime normal := by
    rw [pRank_map_of_injective prime hprime source.subtype Subtype.val_injective]
    rw [← pRank_quotient_map_of_coprime_normal prime hprime radical hcoprime lifted]
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective radical)]
  by_contra hlarge
  have hliftRank : 3 ≤ pRank prime (lifted.map source.subtype) := by
    rw [hrankEqual]
    omega
  exact hescape (normal_subgroup_sylow_rank_forces_containment prime hprime sylow
    hsylow hcore lifted hcontained hliftRank)

theorem pRank_primeCore_quotient_map
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (source : Subgroup ambient)
    [((GLBPrimeCore prime source).subgroupOf source).Normal] (subgroup : Subgroup source) :
    pRank prime (subgroup.map
      (QuotientGroup.mk' ((GLBPrimeCore prime source).subgroupOf source))) =
        pRank prime subgroup := by
  apply pRank_quotient_map_of_coprime_normal prime hprime
  rw [Nat.card_congr ((GLBPrimeCore prime source).subgroupOfEquivOfLe
    (primeCore_le prime source)).toEquiv]
  exact hprime.coprime_iff_not_dvd.mp (primeCore_coprime prime hprime source)

theorem sylow_quotient_equivalence_of_coprime_kernel
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (normal : Subgroup source) [normal.Normal]
    (hcoprime : ¬ prime ∣ Nat.card normal)
    (hquotient : IsPGroup prime (source ⧸ normal)) (sylow : Sylow prime source) :
    Nonempty ((sylow : Subgroup source) ≃* (source ⧸ normal)) := by
  let hom := QuotientGroup.mk' normal
  let quotientSylow := Sylow.mapSurjective (QuotientGroup.mk'_surjective normal) sylow
  have himageTop : (sylow : Subgroup source).map hom = ⊤ := by
    rw [← Sylow.coe_mapSurjective]
    exact (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hinjective := pGroup_quotient_subgroupMap_injective_of_coprime_kernel prime
    Fact.out normal hcoprime (sylow : Subgroup source) sylow.isPGroup'
  let imageEquivalence := MulEquiv.ofBijective (hom.subgroupMap (sylow : Subgroup source))
    ⟨hinjective, hom.subgroupMap_surjective (sylow : Subgroup source)⟩
  let topEquivalence : ((sylow : Subgroup source).map hom) ≃* (⊤ : Subgroup (source ⧸ normal)) :=
    MulEquiv.subgroupCongr himageTop
  exact ⟨imageEquivalence.trans (topEquivalence.trans (Subgroup.topEquiv))⟩

end CFSG.PreuniquenessRankFour.Helpers
