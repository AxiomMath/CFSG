module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SignalizerCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeNonabelian

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem sylow_automorphism_conjugation_equivariant
    {Actor Value : Type*} [Group Actor] [Group Value] [MulDistribMulAction Actor Value]
    (sylowPrime : ℕ) (actingElement : Actor) (conjugator : Value)
    (sylowGroup : Sylow sylowPrime Value) :
    Sylow.pointwiseMulAction.smul actingElement (conjugator • sylowGroup) =
      (actingElement • conjugator) • Sylow.pointwiseMulAction.smul actingElement sylowGroup := by
  let : MulAction Actor (Sylow sylowPrime Value) := Sylow.pointwiseMulAction
  change actingElement • (conjugator • sylowGroup) =
    (actingElement • conjugator) • (actingElement • sylowGroup)
  apply Sylow.ext
  rw [Sylow.pointwise_smul_def, sylow_conjugate_eq_map, Subgroup.pointwise_smul_def,
    sylow_conjugate_eq_map, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  change ((sylowGroup : Subgroup Value).map (MulAut.conj conjugator).toMonoidHom).map
      ((MulDistribMulAction.toMulAut Actor Value) actingElement).toMonoidHom =
    ((sylowGroup : Subgroup Value).map
      ((MulDistribMulAction.toMulAut Actor Value) actingElement).toMonoidHom).map
        (MulAut.conj (actingElement • conjugator)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  simp [MulAut.conj_apply, smul_mul', smul_inv']

@[expose] def sylowTransporterNormalizerEquiv
    {Value : Type*} [Group Value] (sylowPrime : ℕ)
    (first second : Sylow sylowPrime Value) (conjugator : Value)
    (hconjugator : conjugator • first = second) :
    Subgroup.normalizer (first : Set Value) ≃ {element : Value // element • first = second} where
  toFun normalizerElement := ⟨conjugator * normalizerElement, by
    rw [mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr normalizerElement.property, hconjugator]⟩
  invFun element := ⟨conjugator⁻¹ * element, by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [mul_smul, element.property, ← hconjugator, inv_smul_smul]⟩
  left_inv := by
    intro normalizerElement
    apply Subtype.ext
    exact inv_mul_cancel_left _ _
  right_inv := by
    intro element
    apply Subtype.ext
    exact mul_inv_cancel_left _ _

theorem coprime_pGroup_invariant_sylows_fixed_conjugator
    {Actor Value : Type*} [Group Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (actorPrime : ℕ) (hactorPrime : actorPrime.Prime) (hactor : IsPGroup actorPrime Actor)
    (hcoprime : actorPrime.Coprime (Nat.card Value))
    (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime)
    (first second : Sylow sylowPrime Value)
    (hfirst : ∀ actingElement : Actor,
      Sylow.pointwiseMulAction.smul actingElement first = first)
    (hsecond : ∀ actingElement : Actor,
      Sylow.pointwiseMulAction.smul actingElement second = second) :
    ∃ conjugator : Value, conjugator • first = second ∧
      ∀ actingElement : Actor, actingElement • conjugator = conjugator := by
  classical
  let : Fact actorPrime.Prime := ⟨hactorPrime⟩
  let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  let : MulAction Actor (Sylow sylowPrime Value) := Sylow.pointwiseMulAction
  have hfirstFixed : ∀ actingElement : Actor, actingElement • first = first := hfirst
  have hsecondFixed : ∀ actingElement : Actor, actingElement • second = second := hsecond
  let transporter := {element : Value // element • first = second}
  have hpreserved (actingElement : Actor) (element : transporter) :
      (actingElement • (element : Value)) • first = second := by
    have hcompat := sylow_automorphism_conjugation_equivariant sylowPrime actingElement
      (element : Value) first
    change actingElement • ((element : Value) • first) =
      (actingElement • (element : Value)) • (actingElement • first) at hcompat
    rw [element.property, hfirstFixed actingElement, hsecondFixed actingElement] at hcompat
    exact hcompat.symm
  let : MulAction Actor transporter := {
    smul := fun actingElement element => ⟨actingElement • (element : Value),
      hpreserved actingElement element⟩
    one_smul := by
      intro element
      apply Subtype.ext
      exact one_smul _ _
    mul_smul := by
      intro firstActor secondActor element
      apply Subtype.ext
      exact mul_smul _ _ _ }
  obtain ⟨initialConjugator, hinitial⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := Value) first second
  have hcard : Nat.card transporter = Nat.card (Subgroup.normalizer (first : Set Value)) :=
    (Nat.card_congr (sylowTransporterNormalizerEquiv sylowPrime first second
      initialConjugator hinitial)).symm
  have hnotDvd : ¬ actorPrime ∣ Nat.card transporter := by
    rw [hcard]
    exact hactorPrime.coprime_iff_not_dvd.mp (hcoprime.of_dvd_right
      (Subgroup.normalizer (first : Set Value)).card_subgroup_dvd_card)
  obtain ⟨fixedConjugator, hfixed⟩ :=
    hactor.nonempty_fixed_point_of_prime_not_dvd_card transporter hnotDvd
  exact ⟨fixedConjugator, fixedConjugator.property, fun actingElement =>
    congrArg Subtype.val (hfixed actingElement)⟩

theorem coprime_maximal_invariant_prime_subgroup_is_sylow
    {Actor Value : Type*} [Group Actor] [Group Value] [Finite Value]
    (action : Actor →* MulAut Value)
    (actorPrime : ℕ) (hactorPrime : actorPrime.Prime) (hactor : IsPGroup actorPrime Actor)
    (hcoprime : actorPrime.Coprime (Nat.card Value))
    (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime)
    (invariantGroup : Subgroup Value) (hgroup : IsPGroup sylowPrime invariantGroup)
    (hinvariant : ∀ actingElement : Actor,
      invariantGroup.map (action actingElement).toMonoidHom = invariantGroup)
    (hmaximal : ∀ larger : Subgroup Value, IsPGroup sylowPrime larger →
      (∀ actingElement : Actor, larger.map (action actingElement).toMonoidHom = larger) →
      invariantGroup ≤ larger → larger = invariantGroup) :
    ∃ sylowGroup : Sylow sylowPrime Value, (sylowGroup : Subgroup Value) = invariantGroup := by
  classical
  let : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  let normalizer := Subgroup.normalizer (invariantGroup : Set Value)
  have hnormalizerInvariant : ∀ actingElement : Actor, ∀ element ∈ normalizer,
      action actingElement element ∈ normalizer := by
    intro actingElement element helement
    have himage := Subgroup.mem_map_of_mem (action actingElement).toMonoidHom helement
    change action actingElement element ∈ normalizer.map (action actingElement).toMonoidHom at himage
    dsimp only [normalizer] at himage ⊢
    rw [Subgroup.map_equiv_normalizer_eq, hinvariant] at himage
    exact himage
  let normalizerAction := invariantActionHom action normalizer hnormalizerInvariant
  let : MulDistribMulAction Actor normalizer := multiplicativeActionOfMulAutHom normalizerAction
  obtain ⟨normalizerSylow, hfixed⟩ := coprime_pGroup_has_invariant_sylow actorPrime hactorPrime
    hactor (hcoprime.of_dvd_right normalizer.card_subgroup_dvd_card) sylowPrime hsylowPrime
  let liftedSylow := (normalizerSylow : Subgroup normalizer).map normalizer.subtype
  have hliftedGroup : IsPGroup sylowPrime liftedSylow := normalizerSylow.isPGroup'.map _
  have hliftedInvariant : ∀ actingElement : Actor,
      liftedSylow.map (action actingElement).toMonoidHom = liftedSylow := by
    intro actingElement
    have hfixedSubgroup := congrArg (fun subgroup : Sylow sylowPrime normalizer =>
      (subgroup : Subgroup normalizer)) (hfixed actingElement)
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hfixedSubgroup
    change (normalizerSylow : Subgroup normalizer).map
      (normalizerAction actingElement).toMonoidHom = (normalizerSylow : Subgroup normalizer)
      at hfixedSubgroup
    have hmaps : (action actingElement).toMonoidHom.comp normalizer.subtype =
        normalizer.subtype.comp (normalizerAction actingElement).toMonoidHom := rfl
    change ((normalizerSylow : Subgroup normalizer).map normalizer.subtype).map
      (action actingElement).toMonoidHom = _
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map, hfixedSubgroup]
  have hcontained : invariantGroup ≤ liftedSylow := by
    have hinternalGroup : IsPGroup sylowPrime (invariantGroup.subgroupOf normalizer) :=
      hgroup.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
    have hinternalNormal : (invariantGroup.subgroupOf normalizer).Normal :=
      Subgroup.normal_in_normalizer
    let : (invariantGroup.subgroupOf normalizer).Normal := hinternalNormal
    have hinternalLe := hinternalGroup.le_sylow_of_normal normalizerSylow
    have himage := Subgroup.map_mono (f := normalizer.subtype) hinternalLe
    rwa [Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer] at himage
  have hliftedEqual := hmaximal liftedSylow hliftedGroup hliftedInvariant hcontained
  obtain ⟨ambientSylow, hambientLe⟩ := hgroup.exists_le_sylow
  let : Group.IsNilpotent (ambientSylow : Subgroup Value) := ambientSylow.isPGroup'.isNilpotent
  have hself : Subgroup.normalizer
      (invariantGroup.subgroupOf (ambientSylow : Subgroup Value) : Set (ambientSylow : Subgroup Value)) =
        invariantGroup.subgroupOf (ambientSylow : Subgroup Value) := by
    apply le_antisymm
    · rw [← Subgroup.subgroupOf_normalizer_eq hambientLe]
      intro element hnormalizing
      have hnormalizerElement : (element : Value) ∈ normalizer := hnormalizing
      let internalIntersection :=
        (Subgroup.normalizer (invariantGroup : Set Value) ⊓ (ambientSylow : Subgroup Value)).subgroupOf
          normalizer
      have hintersectionGroup : IsPGroup sylowPrime internalIntersection := by
        exact (ambientSylow.isPGroup'.to_inf_right).of_equiv
          (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
      have hintersectionLe : (normalizerSylow : Subgroup normalizer) ≤ internalIntersection := by
        intro internalElement hinternal
        have hgroupElement : (internalElement : Value) ∈ invariantGroup := by
          rw [← hliftedEqual]
          exact Subgroup.mem_map_of_mem normalizer.subtype hinternal
        exact ⟨internalElement.property, hambientLe hgroupElement⟩
      have hintersectionEqual := normalizerSylow.is_maximal' hintersectionGroup hintersectionLe
      have hmemIntersection : (⟨element, hnormalizerElement⟩ : normalizer) ∈ internalIntersection :=
        ⟨hnormalizerElement, element.property⟩
      rw [hintersectionEqual] at hmemIntersection
      have hliftedElement := Subgroup.mem_map_of_mem normalizer.subtype hmemIntersection
      change (element : Value) ∈ liftedSylow at hliftedElement
      rwa [hliftedEqual] at hliftedElement
    · exact Subgroup.le_normalizer
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (ambientSylow : Subgroup Value)))) _ hself
  exact ⟨ambientSylow, le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hambientLe⟩

theorem coprime_maximal_invariant_prime_subgroups_fixed_conjugator
    {Actor Value : Type*} [Group Actor] [Group Value] [Finite Value]
    (action : Actor →* MulAut Value)
    (actorPrime : ℕ) (hactorPrime : actorPrime.Prime) (hactor : IsPGroup actorPrime Actor)
    (hcoprime : actorPrime.Coprime (Nat.card Value))
    (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime) (first second : Subgroup Value)
    (hfirst : IsPGroup sylowPrime first)
    (hfirstInvariant : ∀ actingElement : Actor,
      first.map (action actingElement).toMonoidHom = first)
    (hfirstMaximal : ∀ larger : Subgroup Value, IsPGroup sylowPrime larger →
      (∀ actingElement : Actor, larger.map (action actingElement).toMonoidHom = larger) →
      first ≤ larger → larger = first)
    (hsecond : IsPGroup sylowPrime second)
    (hsecondInvariant : ∀ actingElement : Actor,
      second.map (action actingElement).toMonoidHom = second)
    (hsecondMaximal : ∀ larger : Subgroup Value, IsPGroup sylowPrime larger →
      (∀ actingElement : Actor, larger.map (action actingElement).toMonoidHom = larger) →
      second ≤ larger → larger = second) :
    ∃ conjugator : Value, first.map (MulAut.conj conjugator).toMonoidHom = second ∧
      ∀ actingElement : Actor, action actingElement conjugator = conjugator := by
  let : MulDistribMulAction Actor Value := multiplicativeActionOfMulAutHom action
  obtain ⟨firstSylow, hfirstSylow⟩ := coprime_maximal_invariant_prime_subgroup_is_sylow
    action actorPrime hactorPrime hactor hcoprime sylowPrime hsylowPrime first hfirst
    hfirstInvariant hfirstMaximal
  obtain ⟨secondSylow, hsecondSylow⟩ := coprime_maximal_invariant_prime_subgroup_is_sylow
    action actorPrime hactorPrime hactor hcoprime sylowPrime hsylowPrime second hsecond
    hsecondInvariant hsecondMaximal
  have hfirstFixed : ∀ actingElement : Actor,
      Sylow.pointwiseMulAction.smul actingElement firstSylow = firstSylow := by
    intro actingElement
    let : MulAction Actor (Sylow sylowPrime Value) := Sylow.pointwiseMulAction
    change actingElement • firstSylow = firstSylow
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    change (firstSylow : Subgroup Value).map (action actingElement).toMonoidHom =
      (firstSylow : Subgroup Value)
    rw [hfirstSylow, hfirstInvariant]
  have hsecondFixed : ∀ actingElement : Actor,
      Sylow.pointwiseMulAction.smul actingElement secondSylow = secondSylow := by
    intro actingElement
    let : MulAction Actor (Sylow sylowPrime Value) := Sylow.pointwiseMulAction
    change actingElement • secondSylow = secondSylow
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    change (secondSylow : Subgroup Value).map (action actingElement).toMonoidHom =
      (secondSylow : Subgroup Value)
    rw [hsecondSylow, hsecondInvariant]
  obtain ⟨conjugator, hconjugator, hfixed⟩ := coprime_pGroup_invariant_sylows_fixed_conjugator
    actorPrime hactorPrime hactor hcoprime sylowPrime hsylowPrime firstSylow secondSylow
    hfirstFixed hsecondFixed
  refine ⟨conjugator, ?_, hfixed⟩
  have hsubgroups := congrArg (fun subgroup : Sylow sylowPrime Value =>
    (subgroup : Subgroup Value)) hconjugator
  rwa [sylow_conjugate_eq_map, hfirstSylow, hsecondSylow] at hsubgroups

@[expose] def ambientSubgroupActionHom
    {G : Type*} [Group G] (actingGroup invariantGroup : Subgroup G)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (invariantGroup : Set G)) :
    actingGroup →* MulAut invariantGroup :=
  invariantGroup.normalizerMonoidHom.comp
    (actingGroup.subtype.codRestrict (Subgroup.normalizer (invariantGroup : Set G))
      (fun element => hinvariant element.property))

theorem ambientSubgroupActionHom_apply_coe
    {G : Type*} [Group G] (actingGroup invariantGroup : Subgroup G)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (invariantGroup : Set G))
    (actingElement : actingGroup) (element : invariantGroup) :
    (ambientSubgroupActionHom actingGroup invariantGroup hinvariant actingElement element : G) =
      (actingElement : G) * (element : G) * (actingElement : G)⁻¹ := by
  exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem ambient_subgroup_action_invariant_iff
    {G : Type*} [Group G] (actingGroup invariantGroup subgroup : Subgroup G)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (invariantGroup : Set G))
    (hsubgroup : subgroup ≤ invariantGroup) :
    (∀ actingElement : actingGroup,
      (subgroup.subgroupOf invariantGroup).map
        (ambientSubgroupActionHom actingGroup invariantGroup hinvariant actingElement).toMonoidHom =
          subgroup.subgroupOf invariantGroup) ↔
      actingGroup ≤ Subgroup.normalizer (subgroup : Set G) := by
  let action := ambientSubgroupActionHom actingGroup invariantGroup hinvariant
  have hmaps (actingElement : actingGroup) :
      invariantGroup.subtype.comp (action actingElement).toMonoidHom =
        (MulAut.conj (actingElement : G)).toMonoidHom.comp invariantGroup.subtype := by
    ext element
    exact ambientSubgroupActionHom_apply_coe actingGroup invariantGroup hinvariant actingElement element
  constructor
  · intro hfixed actingElement helement
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hmapped := congrArg (fun internalGroup : Subgroup invariantGroup =>
      internalGroup.map invariantGroup.subtype) (hfixed ⟨actingElement, helement⟩)
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hsubgroup] at hmapped
    exact hmapped
  · intro hnormalizing actingElement
    apply Subgroup.map_injective invariantGroup.subtype_injective
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hsubgroup]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormalizing actingElement.property)

theorem ambient_subgroup_action_image_invariant_iff
    {G : Type*} [Group G] (actingGroup invariantGroup : Subgroup G)
    (hinvariant : actingGroup ≤ Subgroup.normalizer (invariantGroup : Set G))
    (subgroup : Subgroup invariantGroup) :
    (∀ actingElement : actingGroup, subgroup.map
      (ambientSubgroupActionHom actingGroup invariantGroup hinvariant actingElement).toMonoidHom =
        subgroup) ↔
      actingGroup ≤ Subgroup.normalizer (subgroup.map invariantGroup.subtype : Set G) := by
  have hsubgroup : subgroup.map invariantGroup.subtype ≤ invariantGroup := by
    exact (Subgroup.map_le_range _ _).trans invariantGroup.subtype_range.le
  have hrestricted : (subgroup.map invariantGroup.subtype).subgroupOf invariantGroup = subgroup :=
    Subgroup.comap_map_eq_self_of_injective invariantGroup.subtype_injective subgroup
  have hresult := ambient_subgroup_action_invariant_iff actingGroup invariantGroup
    (subgroup.map invariantGroup.subtype) hinvariant hsubgroup
  rwa [hrestricted] at hresult

theorem rank_two_maximal_two_subgroups_common_signalizer_transitivity
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup first second signalizer : Subgroup G)
    (hactor : IsPGroup prime actingGroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hcoprime : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hfirstLe : first ≤ signalizer) (hsecondLe : second ≤ signalizer) :
    ∃ conjugator : G, conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second := by
  let action := ambientSubgroupActionHom actingGroup signalizer hinvariant
  have hfirstInternal : IsPGroup 2 (first.subgroupOf signalizer) :=
    hfirst.1.of_equiv (Subgroup.subgroupOfEquivOfLe hfirstLe).symm
  have hsecondInternal : IsPGroup 2 (second.subgroupOf signalizer) :=
    hsecond.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsecondLe).symm
  have hfirstInvariant : ∀ actingElement : actingGroup,
      (first.subgroupOf signalizer).map (action actingElement).toMonoidHom =
        first.subgroupOf signalizer :=
    (ambient_subgroup_action_invariant_iff actingGroup signalizer first hinvariant hfirstLe).mpr hfirst.2.1
  have hsecondInvariant : ∀ actingElement : actingGroup,
      (second.subgroupOf signalizer).map (action actingElement).toMonoidHom =
        second.subgroupOf signalizer :=
    (ambient_subgroup_action_invariant_iff actingGroup signalizer second hinvariant hsecondLe).mpr hsecond.2.1
  have hmaximal (subgroup : Subgroup G) (hsubgroup : subgroup ≤ signalizer)
      (hglobal : rankTwoMaximalInvariantTwoSubgroup actingGroup subgroup)
      (larger : Subgroup signalizer) (hgroup : IsPGroup 2 larger)
      (hfixed : ∀ actingElement : actingGroup,
        larger.map (action actingElement).toMonoidHom = larger)
      (hinclusion : subgroup.subgroupOf signalizer ≤ larger) :
      larger = subgroup.subgroupOf signalizer := by
    have himageInvariant := (ambient_subgroup_action_image_invariant_iff actingGroup
      signalizer hinvariant larger).mp hfixed
    have himageLe : subgroup ≤ larger.map signalizer.subtype := by
      have himage := Subgroup.map_mono (f := signalizer.subtype) hinclusion
      rwa [Subgroup.map_subgroupOf_eq_of_le hsubgroup] at himage
    have hequal := hglobal.2.2 (larger.map signalizer.subtype) (hgroup.map signalizer.subtype)
      himageInvariant himageLe
    apply Subgroup.map_injective signalizer.subtype_injective
    rwa [Subgroup.map_subgroupOf_eq_of_le hsubgroup]
  obtain ⟨conjugator, hconjugator, hfixed⟩ :=
    coprime_maximal_invariant_prime_subgroups_fixed_conjugator action prime hprime hactor
      hcoprime 2 Nat.prime_two (first.subgroupOf signalizer) (second.subgroupOf signalizer)
      hfirstInternal hfirstInvariant (hmaximal first hfirstLe hfirst)
      hsecondInternal hsecondInvariant (hmaximal second hsecondLe hsecond)
  refine ⟨conjugator, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro actingElement helement
    have hambient := congrArg Subtype.val (hfixed ⟨actingElement, helement⟩)
    rw [ambientSubgroupActionHom_apply_coe] at hambient
    exact mul_inv_eq_iff_eq_mul.mp hambient
  · have hmapped := congrArg (fun subgroup : Subgroup signalizer =>
      subgroup.map signalizer.subtype) hconjugator
    have hmaps : signalizer.subtype.comp (MulAut.conj conjugator).toMonoidHom =
        (MulAut.conj (conjugator : G)).toMonoidHom.comp signalizer.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, hmaps, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hfirstLe,
      Subgroup.map_subgroupOf_eq_of_le hsecondLe] at hmapped
    exact hmapped

theorem rank_two_nontransitive_pair_join_has_prime_divisor
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup first second : Subgroup G)
    (hactor : IsPGroup prime actingGroup)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup actingGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup actingGroup second)
    (hnontransitive : ¬ ∃ conjugator : G,
      conjugator ∈ Subgroup.centralizer (actingGroup : Set G) ∧
        first.map (MulAut.conj conjugator).toMonoidHom = second) :
    prime ∣ Nat.card ↥(first ⊔ second : Subgroup G) := by
  by_contra hnotDvd
  have hcoprime := hprime.coprime_iff_not_dvd.mpr hnotDvd
  have hinvariant : actingGroup ≤ Subgroup.normalizer ((first ⊔ second : Subgroup G) : Set G) :=
    (le_inf hfirst.2.1 hsecond.2.1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup first second)
  exact hnontransitive (rank_two_maximal_two_subgroups_common_signalizer_transitivity
    prime hprime actingGroup first second (first ⊔ second) hactor hfirst hsecond
    hcoprime hinvariant le_sup_left le_sup_right)

theorem rank_two_normalizer_le_of_coprime_maximal_pair_joins
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup overgroup twoGroup : Subgroup G)
    (hactor : IsPGroup prime actingGroup)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup)
    (hcentralizer : Subgroup.centralizer (actingGroup : Set G) ≤ overgroup)
    (hnormalizer : Subgroup.normalizer (twoGroup : Set G) ≤ overgroup)
    (hpairs : ∀ other : Subgroup G, rankTwoMaximalInvariantTwoSubgroup actingGroup other →
      ¬ prime ∣ Nat.card ↥(other ⊔ twoGroup : Subgroup G)) :
    Subgroup.normalizer (actingGroup : Set G) ≤ overgroup := by
  apply rankTwo_normalizer_le_of_signalizer_transitivity actingGroup overgroup twoGroup
    hmaximal hcentralizer hnormalizer
  intro other hother
  have hinvariant : actingGroup ≤
      Subgroup.normalizer ((other ⊔ twoGroup : Subgroup G) : Set G) :=
    (le_inf hother.2.1 hmaximal.2.1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup other twoGroup)
  exact rank_two_maximal_two_subgroups_common_signalizer_transitivity prime hprime
    actingGroup other twoGroup (other ⊔ twoGroup) hactor hother hmaximal
    (hprime.coprime_iff_not_dvd.mpr (hpairs other hother)) hinvariant le_sup_left le_sup_right

theorem rank_two_escaping_normalizer_has_prime_divisible_maximal_pair_join
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup overgroup twoGroup : Subgroup G)
    (hactor : IsPGroup prime actingGroup)
    (hmaximal : rankTwoMaximalInvariantTwoSubgroup actingGroup twoGroup)
    (hcentralizer : Subgroup.centralizer (actingGroup : Set G) ≤ overgroup)
    (hnormalizer : Subgroup.normalizer (twoGroup : Set G) ≤ overgroup)
    (hescape : ¬ Subgroup.normalizer (actingGroup : Set G) ≤ overgroup) :
    ∃ other : Subgroup G, rankTwoMaximalInvariantTwoSubgroup actingGroup other ∧
      prime ∣ Nat.card ↥(other ⊔ twoGroup : Subgroup G) := by
  classical
  by_contra hnone
  push Not at hnone
  exact hescape (rank_two_normalizer_le_of_coprime_maximal_pair_joins prime hprime
    actingGroup overgroup twoGroup hactor hmaximal hcentralizer hnormalizer hnone)

end CFSG.RankThreeCoreUniqueness.Helpers
