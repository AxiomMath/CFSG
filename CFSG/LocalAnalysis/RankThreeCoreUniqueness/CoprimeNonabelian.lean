module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAction

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

universe u

@[expose, instance_reducible]
def multiplicativeActionOfMulAutHom
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value) : MulDistribMulAction Actor Value where
  smul actingElement element := action actingElement element
  one_smul := by
    intro element
    change action 1 element = element
    rw [map_one]
    rfl
  mul_smul := by
    intro first second element
    change action (first * second) element = action first (action second element)
    rw [map_mul]
    rfl
  smul_one := by
    intro actingElement
    exact map_one _
  smul_mul := by
    intro actingElement first second
    exact map_mul _ _ _

@[expose] def characteristicActionHom
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    (hcharacteristic : invariantGroup.Characteristic) : Actor →* MulAut invariantGroup where
  toFun actingElement := {
    toFun := fun element => ⟨action actingElement element,
      (Subgroup.characteristic_iff_le_comap.mp hcharacteristic
        (action actingElement)) element.property⟩
    invFun := fun element => ⟨(action actingElement).symm element,
      (Subgroup.characteristic_iff_le_comap.mp hcharacteristic
        (action actingElement).symm) element.property⟩
    left_inv := by
      intro element
      apply Subtype.ext
      exact (action actingElement).symm_apply_apply _
    right_inv := by
      intro element
      apply Subtype.ext
      exact (action actingElement).apply_symm_apply _
    map_mul' := by
      intro first second
      apply Subtype.ext
      exact map_mul _ _ _ }
  map_one' := by
    ext element
    change action 1 (element : Value) = (element : Value)
    rw [map_one]
    rfl
  map_mul' := by
    intro first second
    ext element
    change action (first * second) (element : Value) =
      action first (action second (element : Value))
    rw [map_mul]
    rfl

theorem abelianization_of_surjective {Value : Type*} [Group Value] :
    Function.Surjective (Abelianization.of : Value →* Abelianization Value) := by
  exact Quotient.mk_surjective

@[expose] def abelianizationActionHom
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value) : Actor →* MulAut (Abelianization Value) where
  toFun actingElement := (action actingElement).abelianizationCongr
  map_one' := by
    ext element
    obtain ⟨preimage, rfl⟩ := abelianization_of_surjective element
    simp only [abelianizationCongr_of, map_one, MulAut.one_apply]
  map_mul' := by
    intro first second
    ext element
    obtain ⟨preimage, rfl⟩ := abelianization_of_surjective element
    simp only [abelianizationCongr_of, map_mul, MulAut.mul_apply]

@[expose] def invariantActionHom
    {Actor Value : Type*} [Group Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    (hinvariant : ∀ actingElement : Actor, ∀ element ∈ invariantGroup,
      action actingElement element ∈ invariantGroup) : Actor →* MulAut invariantGroup where
  toFun actingElement := {
    toFun := fun element => ⟨action actingElement element,
      hinvariant actingElement element element.property⟩
    invFun := fun element => ⟨action actingElement⁻¹ element,
      hinvariant actingElement⁻¹ element element.property⟩
    left_inv := by
      intro element
      apply Subtype.ext
      change action actingElement⁻¹ (action actingElement (element : Value)) = element
      rw [map_inv]
      exact MulAut.inv_apply_self _ _ _
    right_inv := by
      intro element
      apply Subtype.ext
      change action actingElement (action actingElement⁻¹ (element : Value)) = element
      rw [map_inv]
      exact MulAut.apply_inv_self _ _ _
    map_mul' := by
      intro first second
      apply Subtype.ext
      exact map_mul _ _ _ }
  map_one' := by
    ext element
    change action 1 (element : Value) = (element : Value)
    rw [map_one]
    rfl
  map_mul' := by
    intro first second
    ext element
    change action (first * second) (element : Value) =
      action first (action second (element : Value))
    rw [map_mul]
    rfl

@[expose] def monoidHomKernelFiberEquiv
    {Source Target : Type*} [Group Source] [Group Target]
    (homomorphism : Source →* Target) (preimage : Source) :
    homomorphism.ker ≃ {element : Source // homomorphism element = homomorphism preimage} where
  toFun kernelElement := ⟨preimage * kernelElement, by
    simp only [map_mul, MonoidHom.mem_ker.mp kernelElement.property, mul_one]⟩
  invFun element := ⟨preimage⁻¹ * element, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, element.property, inv_mul_cancel]⟩
  left_inv := by
    intro kernelElement
    apply Subtype.ext
    exact inv_mul_cancel_left _ _
  right_inv := by
    intro element
    apply Subtype.ext
    exact mul_inv_cancel_left _ _

theorem coprime_pGroup_fixed_lift
    {Actor Source Target : Type*} [Group Actor] [Group Source] [Group Target] [Finite Source]
    [MulDistribMulAction Actor Source] [MulDistribMulAction Actor Target]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (homomorphism : Source →* Target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ actingElement : Actor, ∀ element : Source,
      homomorphism (actingElement • element) = actingElement • homomorphism element)
    (hcoprime : prime.Coprime (Nat.card homomorphism.ker))
    (element : Target) (hfixed : ∀ actingElement : Actor, actingElement • element = element) :
    ∃ preimage : Source, homomorphism preimage = element ∧
      ∀ actingElement : Actor, actingElement • preimage = preimage := by
  let : Fact prime.Prime := ⟨hprime⟩
  let fiber := {preimage : Source // homomorphism preimage = element}
  let : MulAction Actor fiber := {
    smul := fun actingElement preimage => ⟨actingElement • preimage, by
      rw [hequivariant, preimage.property, hfixed]⟩
    one_smul := by
      intro preimage
      apply Subtype.ext
      exact one_smul _ _
    mul_smul := by
      intro first second preimage
      apply Subtype.ext
      exact mul_smul _ _ _ }
  obtain ⟨initialPreimage, hinitial⟩ := hsurjective element
  have hcard : Nat.card fiber = Nat.card homomorphism.ker := by
    dsimp only [fiber]
    rw [← hinitial]
    exact (Nat.card_congr (monoidHomKernelFiberEquiv homomorphism initialPreimage)).symm
  have hnotDvd : ¬ prime ∣ Nat.card fiber := by
    rw [hcard]
    exact (hprime.coprime_iff_not_dvd.mp hcoprime)
  obtain ⟨fixedPreimage, hfixedPreimage⟩ :=
    hactor.nonempty_fixed_point_of_prime_not_dvd_card fiber hnotDvd
  refine ⟨fixedPreimage, fixedPreimage.property, ?_⟩
  intro actingElement
  exact congrArg Subtype.val (hfixedPreimage actingElement)

theorem finite_prime_coprime_solvable_fixed_planes_generate
    {Value : Type u} [Group Value] [Finite Value] [Group.IsSolvable Value]
    (prime : ℕ) (hprime : prime.Prime)
    (action : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* MulAut Value)
    (overgroup : Subgroup Value) (hcoprime : prime.Coprime (Nat.card Value))
    (hplanes : ∀ first second : ZMod prime × ZMod prime × ZMod prime,
      LinearIndependent (ZMod prime) ![first, second] → ∀ element : Value,
      (∀ coordinate : Multiplicative (ZMod prime × ZMod prime),
        action (coordinatePlaneHom first second coordinate) element = element) →
      element ∈ overgroup) : overgroup = ⊤ := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  have inductiveClaim : ∀ cardinal : ℕ,
      ∀ (ValueGroup : Type u) [Group ValueGroup] [Finite ValueGroup]
        [Group.IsSolvable ValueGroup], Nat.card ValueGroup = cardinal →
      ∀ (groupAction : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →*
        MulAut ValueGroup) (targetGroup : Subgroup ValueGroup),
      prime.Coprime (Nat.card ValueGroup) →
      (∀ first second : ZMod prime × ZMod prime × ZMod prime,
        LinearIndependent (ZMod prime) ![first, second] → ∀ element : ValueGroup,
        (∀ coordinate : Multiplicative (ZMod prime × ZMod prime),
          groupAction (coordinatePlaneHom first second coordinate) element = element) →
        element ∈ targetGroup) → targetGroup = ⊤ := by
    intro cardinal
    induction cardinal using Nat.strong_induction_on with
    | h cardinal inductionHypothesis =>
      intro ValueGroup groupInstance finiteInstance solvableInstance hcardinal
        groupAction targetGroup hgroupCoprime hgroupPlanes
      by_cases hnontrivial : Nontrivial ValueGroup
      · let : Nontrivial ValueGroup := hnontrivial
        let derivedGroup := commutator ValueGroup
        have hderivedCharacteristic : derivedGroup.Characteristic := by
          dsimp only [derivedGroup]
          rw [← derivedSeries_one]
          infer_instance
        have hderivedCard : Nat.card derivedGroup < cardinal := by
          have hproper := (Group.IsSolvable.commutator_lt_top_of_nontrivial ValueGroup).ne
          have hunequal : Nat.card derivedGroup ≠ Nat.card ValueGroup := by
            intro hequal
            exact hproper ((derivedGroup.card_eq_iff_eq_top).mp hequal)
          exact hcardinal ▸ lt_of_le_of_ne derivedGroup.card_le_card_group hunequal
        let derivedAction := characteristicActionHom groupAction derivedGroup hderivedCharacteristic
        have hderivedTop : targetGroup.subgroupOf derivedGroup = ⊤ := by
          apply inductionHypothesis (Nat.card derivedGroup) hderivedCard derivedGroup rfl
            derivedAction (targetGroup.subgroupOf derivedGroup)
          · exact hgroupCoprime.of_dvd_right derivedGroup.card_subgroup_dvd_card
          · intro first second hindependent element hfixed
            exact hgroupPlanes first second hindependent element (fun coordinate =>
              congrArg Subtype.val (hfixed coordinate))
        have hderivedLe : derivedGroup ≤ targetGroup := by
          intro element helement
          exact show (⟨element, helement⟩ : derivedGroup) ∈ targetGroup.subgroupOf derivedGroup from
            hderivedTop ▸ Subgroup.mem_top _
        let quotientAction := abelianizationActionHom groupAction
        let : DistribMulAction (Multiplicative (ZMod prime × ZMod prime × ZMod prime))
            (Additive (Abelianization ValueGroup)) := additiveActionOfMulAutHom quotientAction
        let quotientOvergroup := Subgroup.toAddSubgroup (targetGroup.map Abelianization.of)
        have hquotientCardDvd : Nat.card (Abelianization ValueGroup) ∣ Nat.card ValueGroup := by
          have hdivisibility := Subgroup.card_range_dvd
            (Abelianization.of : ValueGroup →* Abelianization ValueGroup)
          rwa [MonoidHom.range_eq_top_of_surjective _ abelianization_of_surjective,
            Subgroup.card_top] at hdivisibility
        have hquotientTop : quotientOvergroup = ⊤ := by
          apply finite_field_coprime_fixed_planes_generate (FieldType := ZMod prime)
            quotientOvergroup
          · rw [← Nat.card_congr
              (Additive.ofMul : Abelianization ValueGroup ≃ Additive (Abelianization ValueGroup))]
            simpa [Nat.card_eq_fintype_card] using
              hgroupCoprime.of_dvd_right hquotientCardDvd
          · intro first second hindependent element hfirst hsecond
            let planeAction := groupAction.comp (coordinatePlaneHom first second)
            let quotientPlaneAction := quotientAction.comp (coordinatePlaneHom first second)
            let : MulDistribMulAction (Multiplicative (ZMod prime × ZMod prime)) ValueGroup :=
              multiplicativeActionOfMulAutHom planeAction
            let : MulDistribMulAction (Multiplicative (ZMod prime × ZMod prime))
                (Abelianization ValueGroup) := multiplicativeActionOfMulAutHom quotientPlaneAction
            have hactor : IsPGroup prime (Multiplicative (ZMod prime × ZMod prime)) := by
              apply IsPGroup.of_card (n := 2)
              change Nat.card (ZMod prime × ZMod prime) = prime ^ 2
              rw [Nat.card_prod, Nat.card_zmod, pow_two]
            have hequivariant : ∀ actingElement : Multiplicative (ZMod prime × ZMod prime),
                ∀ sourceElement : ValueGroup,
                Abelianization.of (actingElement • sourceElement) =
                  actingElement • Abelianization.of sourceElement := by
              intro actingElement sourceElement
              exact (abelianizationCongr_of
                (groupAction (coordinatePlaneHom first second actingElement)) sourceElement).symm
            have hfixed : ∀ actingElement : Multiplicative (ZMod prime × ZMod prime),
                actingElement • Additive.toMul element = Additive.toMul element := by
              intro actingElement
              have hsplit : coordinatePlaneHom first second actingElement =
                  scalarLineHom first (Multiplicative.ofAdd (Multiplicative.toAdd actingElement).1) *
                  scalarLineHom second (Multiplicative.ofAdd (Multiplicative.toAdd actingElement).2) := rfl
              change quotientAction (coordinatePlaneHom first second actingElement)
                (Additive.toMul element) = Additive.toMul element
              have hadditiveFixed : coordinatePlaneHom first second actingElement • element =
                  element := by
                rw [hsplit, mul_smul, hsecond, hfirst]
              exact congrArg Additive.toMul hadditiveFixed
            obtain ⟨preimage, hpreimage, hpreimageFixed⟩ := coprime_pGroup_fixed_lift
              prime hprime hactor Abelianization.of abelianization_of_surjective
              hequivariant (hgroupCoprime.of_dvd_right
                (Abelianization.of : ValueGroup →* Abelianization ValueGroup).ker.card_subgroup_dvd_card)
              (Additive.toMul element) hfixed
            exact ⟨preimage, hgroupPlanes first second hindependent preimage hpreimageFixed,
              hpreimage⟩
        have hquotientImage : targetGroup.map Abelianization.of = ⊤ := by
          exact Subgroup.toAddSubgroup.injective hquotientTop
        have hcomap := congrArg
          (fun subgroup : Subgroup (Abelianization ValueGroup) =>
            subgroup.comap (Abelianization.of : ValueGroup →* Abelianization ValueGroup))
          hquotientImage
        rwa [Subgroup.comap_map_eq, Abelianization.ker_of,
          sup_eq_left.mpr hderivedLe, Subgroup.comap_top] at hcomap
      · let : Subsingleton ValueGroup := not_nontrivial_iff_subsingleton.mp hnontrivial
        apply top_unique
        intro element _
        simpa only [Subsingleton.elim element (1 : ValueGroup)] using targetGroup.one_mem
  exact inductiveClaim (Nat.card Value) Value rfl action overgroup hcoprime hplanes

theorem coprime_pGroup_has_invariant_sylow
    {Actor Value : Type*} [Group Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (actorPrime : ℕ) (hactorPrime : actorPrime.Prime) (hactor : IsPGroup actorPrime Actor)
    (hcoprime : actorPrime.Coprime (Nat.card Value))
    (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime) :
    ∃ sylowGroup : Sylow sylowPrime Value,
      ∀ actingElement : Actor, actingElement • sylowGroup = sylowGroup := by
  let : Fact actorPrime.Prime := ⟨hactorPrime⟩
  let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  let : MulAction Actor (Sylow sylowPrime Value) := Sylow.pointwiseMulAction
  let sylowGroup : Sylow sylowPrime Value := Classical.choice inferInstance
  have hcardDvd : Nat.card (Sylow sylowPrime Value) ∣ Nat.card Value := by
    exact (Sylow.card_dvd_index sylowGroup).trans
      ⟨Nat.card (sylowGroup : Subgroup Value), sylowGroup.index_mul_card.symm⟩
  have hnotDvd : ¬ actorPrime ∣ Nat.card (Sylow sylowPrime Value) := by
    exact hactorPrime.coprime_iff_not_dvd.mp (hcoprime.of_dvd_right hcardDvd)
  exact hactor.nonempty_fixed_point_of_prime_not_dvd_card (Sylow sylowPrime Value) hnotDvd

theorem finite_prime_coprime_fixed_planes_generate
    {Value : Type u} [Group Value] [Finite Value]
    (prime : ℕ) (hprime : prime.Prime)
    (action : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* MulAut Value)
    (overgroup : Subgroup Value) (hcoprime : prime.Coprime (Nat.card Value))
    (hplanes : ∀ first second : ZMod prime × ZMod prime × ZMod prime,
      LinearIndependent (ZMod prime) ![first, second] → ∀ element : Value,
      (∀ coordinate : Multiplicative (ZMod prime × ZMod prime),
        action (coordinatePlaneHom first second coordinate) element = element) →
      element ∈ overgroup) : overgroup = ⊤ := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : MulDistribMulAction (Multiplicative (ZMod prime × ZMod prime × ZMod prime)) Value :=
    multiplicativeActionOfMulAutHom action
  have hactor : IsPGroup prime (Multiplicative (ZMod prime × ZMod prime × ZMod prime)) := by
    apply IsPGroup.of_card (n := 3)
    change Nat.card (ZMod prime × ZMod prime × ZMod prime) = prime ^ 3
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_prod, Nat.card_zmod]
    ring
  have hinvariantSylowLe : ∀ sylowPrime : ℕ, sylowPrime.Prime →
      ∃ sylowGroup : Sylow sylowPrime Value, (sylowGroup : Subgroup Value) ≤ overgroup := by
    intro sylowPrime hsylowPrime
    let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
    obtain ⟨sylowGroup, hfixed⟩ := coprime_pGroup_has_invariant_sylow prime hprime
      hactor hcoprime sylowPrime hsylowPrime
    have hinvariant : ∀ actingElement : Multiplicative (ZMod prime × ZMod prime × ZMod prime),
        ∀ element ∈ (sylowGroup : Subgroup Value),
        action actingElement element ∈ (sylowGroup : Subgroup Value) := by
      intro actingElement element helement
      have hmembership := Subgroup.smul_mem_pointwise_smul element actingElement
        (sylowGroup : Subgroup Value) helement
      have hsubgroupFixed := congrArg (fun subgroup : Sylow sylowPrime Value =>
        (subgroup : Subgroup Value)) (hfixed actingElement)
      rw [Sylow.pointwise_smul_def] at hsubgroupFixed
      rwa [hsubgroupFixed] at hmembership
    let sylowAction := invariantActionHom action (sylowGroup : Subgroup Value) hinvariant
    let : Group.IsNilpotent (sylowGroup : Subgroup Value) := sylowGroup.isPGroup'.isNilpotent
    have hfull : overgroup.subgroupOf (sylowGroup : Subgroup Value) = ⊤ := by
      apply finite_prime_coprime_solvable_fixed_planes_generate prime hprime sylowAction
        (overgroup.subgroupOf (sylowGroup : Subgroup Value))
      · exact hcoprime.of_dvd_right (sylowGroup : Subgroup Value).card_subgroup_dvd_card
      · intro first second hindependent element helementFixed
        exact hplanes first second hindependent element (fun coordinate =>
          congrArg Subtype.val (helementFixed coordinate))
    refine ⟨sylowGroup, ?_⟩
    intro element helement
    exact show (⟨element, helement⟩ : (sylowGroup : Subgroup Value)) ∈
        overgroup.subgroupOf (sylowGroup : Subgroup Value) from
      hfull ▸ Subgroup.mem_top _
  have hcardDvd : Nat.card Value ∣ Nat.card overgroup := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro sylowPrime exponent hsylowPrime hpowerDvd
    let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
    obtain ⟨sylowGroup, hinclusion⟩ := hinvariantSylowLe sylowPrime hsylowPrime
    have hfactorBound := (hsylowPrime.pow_dvd_iff_le_factorization
      (Nat.ne_of_gt (Nat.card_pos (α := Value)))).mp hpowerDvd
    have hdivisibility : sylowPrime ^ exponent ∣ Nat.card (sylowGroup : Subgroup Value) := by
      rw [Sylow.card_eq_multiplicity]
      exact pow_dvd_pow _ hfactorBound
    exact hdivisibility.trans (Subgroup.card_dvd_of_le hinclusion)
  exact overgroup.card_eq_iff_eq_top.mp
    (Nat.dvd_antisymm overgroup.card_subgroup_dvd_card hcardDvd)

open CFSG.Open

theorem embedded_rank_three_signalizer_le_of_plane_centralizers
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (signalizer overgroup : Subgroup G)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer))
    (hcentralizers : ∀ first second : ZMod prime × ZMod prime × ZMod prime,
      LinearIndependent (ZMod prime) ![first, second] →
      signalizer ⊓ Subgroup.centralizer
        ((embedding.comp (coordinatePlaneHom first second)).range : Set G) ≤ overgroup) :
    signalizer ≤ overgroup := by
  let normalizerHom := embedding.codRestrict (Subgroup.normalizer (signalizer : Set G))
    (fun element => hinvariant ⟨element, rfl⟩)
  let action := signalizer.normalizerMonoidHom.comp normalizerHom
  have hfull : overgroup.subgroupOf signalizer = ⊤ := by
    apply finite_prime_coprime_fixed_planes_generate prime hprime action
      (overgroup.subgroupOf signalizer) hcoprime
    intro first second hindependent element hfixed
    apply hcentralizers first second hindependent
    refine ⟨element.property, ?_⟩
    change (element : G) ∈ Subgroup.centralizer
      ((embedding.comp (coordinatePlaneHom first second)).range : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro actingElement ⟨coordinate, rfl⟩
    have hambient := congrArg Subtype.val (hfixed coordinate)
    change ↑(signalizer.normalizerMonoidHom
      (normalizerHom (coordinatePlaneHom first second coordinate)) element) =
        (element : G) at hambient
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hambient
    exact mul_inv_eq_iff_eq_mul.mp hambient
  intro element helement
  exact show (⟨element, helement⟩ : signalizer) ∈ overgroup.subgroupOf signalizer from
    hfull ▸ Subgroup.mem_top _

theorem embedded_rank_three_signalizer_le_aschCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding) (ambient signalizer : Subgroup G)
    (hinclusion : embedding.range ≤ ambient)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) :
    signalizer ≤ rankThreeAschCore 2 prime ambient := by
  apply embedded_rank_three_signalizer_le_of_plane_centralizers prime hprime embedding
    signalizer _ hinvariant hcoprime
  intro first second hindependent
  have hplaneInclusion : (embedding.comp (coordinatePlaneHom first second)).range ≤
      embedding.range := by
    rintro element ⟨coordinate, rfl⟩
    exact ⟨coordinatePlaneHom first second coordinate, rfl⟩
  have hfullCore := gamma_of_abelian_rank_three_le_aschCore 2 prime hprime.one_lt
    ambient embedding.range hinclusion (by infer_instance)
    (embedded_coordinate_rank_at_least_three prime hprime embedding hinjective)
  exact (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((gamma_normalizer_le 2 prime embedding.range _ hplaneInclusion
      (embedded_coordinate_plane_rank_at_least_two prime hprime embedding hinjective
        first second hindependent)).trans hfullCore)

end CFSG.RankThreeCoreUniqueness.Helpers
