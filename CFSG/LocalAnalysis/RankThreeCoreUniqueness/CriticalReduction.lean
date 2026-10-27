module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.BaerTrick

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

universe u

theorem top_lowerCentralSeries_characteristic
    {Value : Type*} [Group Value] (index : ℕ) :
    ((⊤ : Subgroup Value).lowerCentralSeries index).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  rw [Subgroup.map_lowerCentralSeries, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.map_equiv_top]

theorem lowerCentralSeries_le_center_of_next_eq_bot
    {Value : Type*} [Group Value] (index : ℕ)
    (hnext : (⊤ : Subgroup Value).lowerCentralSeries (index + 1) = ⊥) :
    (⊤ : Subgroup Value).lowerCentralSeries index ≤ Subgroup.center Value := by
  rw [Subgroup.lowerCentralSeries_succ] at hnext
  have hcentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hnext
  simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hcentralizes

theorem commutator_centralizing_of_commutator_central
    {Value : Type*} [Group Value] (subgroup : Subgroup Value)
    (hcentral : ⁅subgroup, (⊤ : Subgroup Value)⁆ ≤ Subgroup.center Value) :
    commutator Value ≤ Subgroup.centralizer (subgroup : Set Value) := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  have hreverse : ⁅(⊤ : Subgroup Value), subgroup⁆ ≤ Subgroup.center Value := by
    rwa [Subgroup.commutator_comm]
  have hfirst : ⁅⁅(⊤ : Subgroup Value), subgroup⁆, (⊤ : Subgroup Value)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hreverse (le_rfl : (⊤ : Subgroup Value) ≤ ⊤)).trans
      (le_of_eq (Subgroup.commutator_center_left (⊤ : Subgroup Value)))
  have hsecond : ⁅⁅subgroup, (⊤ : Subgroup Value)⁆, (⊤ : Subgroup Value)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hcentral (le_rfl : (⊤ : Subgroup Value) ≤ ⊤)).trans
      (le_of_eq (Subgroup.commutator_center_left (⊤ : Subgroup Value)))
  exact Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := (⊤ : Subgroup Value)) (H₂ := (⊤ : Subgroup Value)) (H₃ := subgroup)
    hfirst hsecond

theorem nilpotent_class_two_of_characteristic_abelian_central
    {Value : Type*} [Group Value] [Group.IsNilpotent Value]
    (hcharAbelian : ∀ subgroup : Subgroup Value, subgroup.Characteristic →
      IsMulCommutative subgroup → subgroup ≤ Subgroup.center Value) :
    commutator Value ≤ Subgroup.center Value := by
  have inductiveClaim : ∀ index : ℕ,
      (⊤ : Subgroup Value).lowerCentralSeries index = ⊥ →
      commutator Value ≤ Subgroup.center Value := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index inductionHypothesis =>
      intro hvanishing
      by_cases hsmall : index ≤ 2
      · have htwo : (⊤ : Subgroup Value).lowerCentralSeries 2 = ⊥ := by
          apply le_bot_iff.mp
          exact ((Subgroup.lowerCentralSeries_antitone ⊤) hsmall).trans (le_of_eq hvanishing)
        simpa only [Subgroup.top_lowerCentralSeries_one] using
          lowerCentralSeries_le_center_of_next_eq_bot 1 htwo
      · obtain ⟨previous, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ index by omega)
        have hpenultimate := lowerCentralSeries_le_center_of_next_eq_bot (previous + 1)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvanishing)
        let subgroup := (⊤ : Subgroup Value).lowerCentralSeries previous
        have hcommutatorCentral : ⁅subgroup, (⊤ : Subgroup Value)⁆ ≤ Subgroup.center Value := by
          rw [← Subgroup.lowerCentralSeries_succ]
          exact hpenultimate
        have hcommutatorCentralizes :=
          commutator_centralizing_of_commutator_central subgroup hcommutatorCentral
        have hsubgroupDerived : subgroup ≤ commutator Value := by
          rw [← Subgroup.top_lowerCentralSeries_one]
          exact Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
        have habelian : IsMulCommutative subgroup :=
          Subgroup.le_centralizer_iff_isMulCommutative.mp
            (hsubgroupDerived.trans hcommutatorCentralizes)
        have hcentral := hcharAbelian subgroup (top_lowerCentralSeries_characteristic previous) habelian
        have hnext := Subgroup.lowerCentralSeries_succ_eq_bot ⊤ hcentral
        apply inductionHypothesis (previous + 1) (by omega) hnext
  have hnilpotentTop : Group.IsNilpotent (⊤ : Subgroup Value) := inferInstance
  obtain ⟨index, hvanishing⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries ⊤).mp hnilpotentTop
  exact inductiveClaim index hvanishing

theorem coprime_action_trivial_of_normal_subgroup_and_centralizer_fixed
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (fixedGroup : Subgroup Value) (hnormal : fixedGroup.Normal)
    (hfixed : ∀ actingElement : Actor, ∀ element ∈ fixedGroup,
      actingElement • element = element)
    (hcentralizerFixed : ∀ actingElement : Actor,
      ∀ element ∈ Subgroup.centralizer (fixedGroup : Set Value),
      actingElement • element = element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  apply coprime_action_trivial_of_fixed_displacements hcoprime
  intro actingElement element
  apply hcentralizerFixed actingElement
  apply Subgroup.mem_centralizer_iff.mpr
  intro fixedElement hfixedElement
  have hconjugate := hfixed actingElement (element * fixedElement * element⁻¹)
    (hnormal.conj_mem fixedElement hfixedElement element)
  rw [smul_mul', smul_mul', smul_inv', hfixed actingElement fixedElement hfixedElement]
    at hconjugate
  have hequality := congrArg (fun value : Value =>
    element⁻¹ * value * (actingElement • element)) hconjugate
  have hcommute : (element⁻¹ * actingElement • element) * fixedElement =
      fixedElement * (element⁻¹ * actingElement • element) := by
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hequality
  exact hcommute.symm

theorem odd_pGroup_normalized_actor_fixed_order_prime_lemma
    {Actor OtherActor : Type*} {Value : Type u}
    [Group Actor] [Group OtherActor] [Finite OtherActor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hactor : IsPGroup prime Actor) (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (normalizingAction : Actor →* MulAut OtherActor)
    (hcompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, element ^ prime = 1 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  have inductiveClaim : ∀ cardinal : ℕ,
      ∀ (ValueGroup : Type u) [Group ValueGroup] [Finite ValueGroup],
      Nat.card ValueGroup = cardinal →
      ∀ (actorAction : Actor →* MulAut ValueGroup)
        (otherAction : OtherActor →* MulAut ValueGroup),
      IsPGroup prime ValueGroup → (Nat.card ValueGroup).Coprime (Nat.card OtherActor) →
      (∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : ValueGroup,
        actorAction actingElement (otherAction otherElement element) =
          otherAction (normalizingAction actingElement otherElement)
            (actorAction actingElement element)) →
      (∀ element : ValueGroup, element ^ prime = 1 →
        (∀ actingElement : Actor, actorAction actingElement element = element) →
        ∀ otherElement : OtherActor, otherAction otherElement element = element) →
      ∀ otherElement : OtherActor, ∀ element : ValueGroup,
        otherAction otherElement element = element := by
    intro cardinal
    induction cardinal using Nat.strong_induction_on with
    | h cardinal inductionHypothesis =>
      intro ValueGroup groupInstance finiteInstance hcardinal actorAction otherAction
        hgroup hgroupCoprime hactionsCompatibility hfixedCentralized
      let : MulDistribMulAction Actor ValueGroup :=
        multiplicativeActionOfMulAutHom actorAction
      let : MulDistribMulAction OtherActor ValueGroup :=
        multiplicativeActionOfMulAutHom otherAction
      let : Group.IsNilpotent ValueGroup := hgroup.isNilpotent
      by_cases hcharAbelian : ∀ subgroup : Subgroup ValueGroup, subgroup.Characteristic →
          IsMulCommutative subgroup → subgroup ≤ Subgroup.center ValueGroup
      · exact class_two_odd_pGroup_normalized_actor_fixed_order_prime_lemma
          prime hprime hodd hactor hgroup
          (nilpotent_class_two_of_characteristic_abelian_central hcharAbelian)
          hgroupCoprime normalizingAction hactionsCompatibility hfixedCentralized
      · push Not at hcharAbelian
        obtain ⟨fixedGroup, hcharacteristic, habelian, hnoncentral⟩ := hcharAbelian
        let : fixedGroup.Characteristic := hcharacteristic
        have hproper : fixedGroup ≠ ⊤ := by
          intro hequal
          apply hnoncentral
          have hcommutative : IsMulCommutative ValueGroup := by
            rw [hequal] at habelian
            exact isMulCommutative_iff.mpr (fun first second => congrArg Subtype.val
              (isMulCommutative_iff.mp habelian
                (⟨first, Subgroup.mem_top _⟩ : (⊤ : Subgroup ValueGroup))
                (⟨second, Subgroup.mem_top _⟩ : (⊤ : Subgroup ValueGroup))))
          let : IsMulCommutative ValueGroup := hcommutative
          rw [Subgroup.center_eq_top]
          exact le_top
        have hcentralizerProper : Subgroup.centralizer (fixedGroup : Set ValueGroup) ≠ ⊤ := by
          intro hequal
          apply hnoncentral
          intro element helement
          apply Subgroup.mem_center_iff.mpr
          intro otherElement
          have hcentralizing : otherElement ∈
              Subgroup.centralizer (fixedGroup : Set ValueGroup) := by
            rw [hequal]
            exact Subgroup.mem_top _
          exact (Subgroup.mem_centralizer_iff.mp hcentralizing element helement).symm
        have hsubgroupFixed (invariantGroup : Subgroup ValueGroup)
            (hinvariant : invariantGroup.Characteristic) (hproperGroup : invariantGroup ≠ ⊤) :
            ∀ otherElement : OtherActor, ∀ element ∈ invariantGroup,
            otherAction otherElement element = element := by
          have hcard : Nat.card invariantGroup < cardinal := by
            have hne : Nat.card invariantGroup ≠ Nat.card ValueGroup := by
              intro hequal
              exact hproperGroup (invariantGroup.card_eq_iff_eq_top.mp hequal)
            exact hcardinal ▸ lt_of_le_of_ne invariantGroup.card_le_card_group hne
          let subgroupActorAction := characteristicActionHom actorAction invariantGroup hinvariant
          let subgroupOtherAction := characteristicActionHom otherAction invariantGroup hinvariant
          have hresult : ∀ otherElement : OtherActor, ∀ element : invariantGroup,
              subgroupOtherAction otherElement element = element := by
            apply inductionHypothesis (Nat.card invariantGroup) hcard invariantGroup rfl
              subgroupActorAction subgroupOtherAction (hgroup.to_subgroup invariantGroup)
              (hgroupCoprime.of_dvd_left invariantGroup.card_subgroup_dvd_card)
            · intro actingElement otherElement element
              apply Subtype.ext
              exact hactionsCompatibility actingElement otherElement element
            · intro element hpower hfixed otherElement
              apply Subtype.ext
              exact hfixedCentralized element (congrArg Subtype.val hpower)
                (fun actingElement => congrArg Subtype.val (hfixed actingElement)) otherElement
          intro otherElement element helement
          exact congrArg Subtype.val (hresult otherElement ⟨element, helement⟩)
        exact coprime_action_trivial_of_normal_subgroup_and_centralizer_fixed
          hgroupCoprime fixedGroup (by infer_instance)
          (hsubgroupFixed fixedGroup hcharacteristic hproper)
          (hsubgroupFixed (Subgroup.centralizer (fixedGroup : Set ValueGroup))
            (by infer_instance) hcentralizerProper)
  exact inductiveClaim (Nat.card Value) Value rfl
    (MulDistribMulAction.toMulAut Actor Value) (MulDistribMulAction.toMulAut OtherActor Value)
    hvalue hcoprime hcompatibility hcentralizes

end CFSG.RankThreeCoreUniqueness.Helpers
