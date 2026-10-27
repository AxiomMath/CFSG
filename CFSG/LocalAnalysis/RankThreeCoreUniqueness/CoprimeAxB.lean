module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeSylowTransitivity

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

universe u

@[expose] def coprimeActionTraceHom
    {Actor Value : Type*} [Group Actor] [Fintype Actor] [AddCommGroup Value]
    [DistribMulAction Actor Value] : Value →+ Value where
  toFun := coprimeActionTrace (Actor := Actor)
  map_zero' := by
    simp [coprimeActionTrace]
  map_add' := by
    intro first second
    simp only [coprimeActionTrace, smul_add, Finset.sum_add_distrib]

theorem coprimeActionTrace_smul_input
    {Actor Value : Type*} [Group Actor] [Fintype Actor] [AddCommGroup Value]
    [DistribMulAction Actor Value] (actingElement : Actor) (element : Value) :
    coprimeActionTrace (Actor := Actor) (actingElement • element) =
      coprimeActionTrace (Actor := Actor) element := by
  unfold coprimeActionTrace
  exact Fintype.sum_equiv (Equiv.mulRight actingElement)
    (fun other => other • actingElement • element) (fun other => other • element)
    (fun other => (mul_smul other actingElement element).symm)

theorem abelian_pGroup_trace_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (htraceCommute : ∀ actingElement : Actor, ∀ element : Value,
      coprimeActionTrace (Actor := OtherActor) (actingElement • element) =
        actingElement • coprimeActionTrace (Actor := OtherActor) element)
    (hcentralizes : ∀ element : Value, prime • element = 0 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  let : Fact prime.Prime := ⟨hprime⟩
  let trace := coprimeActionTraceHom (Actor := OtherActor) (Value := Value)
  let traceKernel := trace.ker
  have htraceCommuteHom (actingElement : Actor) (element : Value) :
      trace (actingElement • element) = actingElement • trace element :=
    htraceCommute actingElement element
  let : DistribMulAction Actor traceKernel := {
    smul := fun actingElement element => ⟨actingElement • (element : Value), by
      change trace (actingElement • (element : Value)) = 0
      rw [htraceCommuteHom, element.property, smul_zero]⟩
    one_smul := by
      intro element
      apply Subtype.ext
      exact one_smul _ _
    mul_smul := by
      intro first second element
      apply Subtype.ext
      exact mul_smul _ _ _
    smul_zero := by
      intro actingElement
      apply Subtype.ext
      exact smul_zero _
    smul_add := by
      intro actingElement first second
      apply Subtype.ext
      exact smul_add _ _ _ }
  have hkernelPGroup : IsPGroup prime (Multiplicative traceKernel) := by
    have hexponent := isPGroup_iff_pow_pow_eq_one.mp hvalue
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro element
    obtain ⟨exponent, hpower⟩ := hexponent
      (Multiplicative.ofAdd ((Multiplicative.toAdd element : traceKernel) : Value))
    refine ⟨exponent, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hpower
  have hkernelFixedZero (element : traceKernel)
      (hkilled : prime • element = 0)
      (hfixed : ∀ actingElement : Actor, actingElement • element = element) : element = 0 := by
    apply Subtype.ext
    apply (nsmulCoprime hcoprime).injective
    rw [nsmulCoprime_apply, nsmulCoprime_apply, AddSubgroup.coe_zero, nsmul_zero]
    have hotherFixed := hcentralizes (element : Value) (congrArg Subtype.val hkilled)
      (fun actingElement => congrArg Subtype.val (hfixed actingElement))
    have htrace := coprimeActionTrace_of_fixed (Actor := OtherActor) (element : Value) hotherFixed
    exact htrace.symm.trans element.property
  have hkernelTrivial : Subsingleton traceKernel := by
    by_contra hnontrivial
    let : Nontrivial traceKernel := not_subsingleton_iff_nontrivial.mp hnontrivial
    let : Nontrivial (Multiplicative traceKernel) :=
      Multiplicative.toAdd.symm.nontrivial
    obtain ⟨exponent, hpositive, hcard⟩ := hkernelPGroup.nontrivial_iff_card.mp inferInstance
    have hcardKernel := Nat.card_congr
      (Multiplicative.toAdd : Multiplicative traceKernel ≃ traceKernel)
    have hdivisibility : prime ∣ Nat.card traceKernel := by
      rw [← hcardKernel, hcard]
      exact dvd_pow_self _ (Nat.ne_of_gt hpositive)
    obtain ⟨element, hfixed, hnonzero⟩ :=
      hactor.exists_fixed_point_of_prime_dvd_card_of_fixed_point traceKernel hdivisibility
        (a := 0) (fun actingElement => smul_zero actingElement)
    let fixedKernel := FixedPoints.addSubgroup Actor traceKernel
    have hfixedKernelPGroup : IsPGroup prime (Multiplicative fixedKernel) := by
      have hexponent := isPGroup_iff_pow_pow_eq_one.mp hkernelPGroup
      apply isPGroup_iff_pow_pow_eq_one.mpr
      intro fixedElement
      obtain ⟨exponent, hpower⟩ := hexponent
        (Multiplicative.ofAdd ((Multiplicative.toAdd fixedElement : fixedKernel) : traceKernel))
      refine ⟨exponent, ?_⟩
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd hpower
    have hfixedKernelNontrivial : Nontrivial fixedKernel := by
      apply not_subsingleton_iff_nontrivial.mp
      intro htrivial
      have hequality := htrivial.elim (⟨element, hfixed⟩ : fixedKernel) 0
      exact hnonzero (congrArg Subtype.val hequality).symm
    let : Nontrivial (Multiplicative fixedKernel) := by infer_instance
    obtain ⟨fixedExponent, hfixedPositive, hfixedCard⟩ :=
      hfixedKernelPGroup.nontrivial_iff_card.mp inferInstance
    have hfixedDivisibility : prime ∣ Nat.card fixedKernel := by
      rw [← Nat.card_congr (Multiplicative.toAdd : Multiplicative fixedKernel ≃ fixedKernel),
        hfixedCard]
      exact dvd_pow_self _ (Nat.ne_of_gt hfixedPositive)
    obtain ⟨primeElement, hprimeOrder⟩ := exists_prime_addOrderOf_dvd_card' prime hfixedDivisibility
    have hprimeKilled : prime • (primeElement : traceKernel) = 0 := by
      have hpower : prime • primeElement = 0 := by
        rw [← hprimeOrder]
        exact addOrderOf_nsmul_eq_zero primeElement
      exact congrArg Subtype.val hpower
    have hprimeZero := hkernelFixedZero (primeElement : traceKernel) hprimeKilled
      primeElement.property
    have hprimeElementZero : primeElement = 0 := Subtype.ext hprimeZero
    rw [hprimeElementZero, addOrderOf_zero] at hprimeOrder
    exact hprime.ne_one hprimeOrder.symm
  have htraceInjective : Function.Injective trace := by
    apply (AddMonoidHom.ker_eq_bot_iff trace).mp
    apply le_bot_iff.mp
    intro element helement
    have hequal := hkernelTrivial.elim (⟨element, helement⟩ : traceKernel) 0
    exact congrArg Subtype.val hequal
  intro otherElement element
  apply htraceInjective
  exact coprimeActionTrace_smul_input otherElement element

theorem abelian_pGroup_trace_fixed_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (htraceCommute : ∀ actingElement : Actor, ∀ element : Value,
      coprimeActionTrace (Actor := OtherActor) (actingElement • element) =
        actingElement • coprimeActionTrace (Actor := OtherActor) element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  exact abelian_pGroup_trace_fixed_order_prime_lemma prime hprime hactor hvalue hcoprime
    htraceCommute (fun element _ => hcentralizes element)

theorem abelian_pGroup_axb_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  apply abelian_pGroup_trace_fixed_lemma prime hprime hactor hvalue hcoprime
    (hcentralizes := hcentralizes)
  intro actingElement element
  change (∑ otherElement : OtherActor, otherElement • actingElement • element) =
    actingElement • ∑ otherElement : OtherActor, otherElement • element
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl
    (fun otherElement _ => (hcommute actingElement otherElement element).symm)

theorem abelian_pGroup_normalized_actor_fixed_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (normalizingAction : Actor →* MulAut OtherActor)
    (hcompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  apply abelian_pGroup_trace_fixed_lemma prime hprime hactor hvalue hcoprime
    (hcentralizes := hcentralizes)
  intro actingElement element
  change (∑ otherElement : OtherActor, otherElement • actingElement • element) =
    actingElement • ∑ otherElement : OtherActor, otherElement • element
  rw [Finset.smul_sum]
  apply (Fintype.sum_equiv (normalizingAction actingElement).toEquiv
    (fun otherElement => actingElement • otherElement • element)
    (fun otherElement => otherElement • actingElement • element)
    (fun otherElement => hcompatibility actingElement otherElement element)).symm

theorem abelian_pGroup_normalized_actor_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Fintype OtherActor]
    [AddCommGroup Value] [Finite Value]
    [DistribMulAction Actor Value] [DistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime (Multiplicative Value))
    (hcoprime : (Nat.card Value).Coprime (Fintype.card OtherActor))
    (normalizingAction : Actor →* MulAut OtherActor)
    (hcompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, prime • element = 0 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  apply abelian_pGroup_trace_fixed_order_prime_lemma prime hprime hactor hvalue hcoprime
    (hcentralizes := hcentralizes)
  intro actingElement element
  change (∑ otherElement : OtherActor, otherElement • actingElement • element) =
    actingElement • ∑ otherElement : OtherActor, otherElement • element
  rw [Finset.smul_sum]
  exact (Fintype.sum_equiv (normalizingAction actingElement).toEquiv
    (fun otherElement => actingElement • otherElement • element)
    (fun otherElement => otherElement • actingElement • element)
    (fun otherElement => hcompatibility actingElement otherElement element)).symm

theorem coprime_element_fixed_of_fixed_displacement
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (actingElement : Actor) (element : Value)
    (hfixed : actingElement • (element⁻¹ * actingElement • element) =
      element⁻¹ * actingElement • element) : actingElement • element = element := by
  let displacement := element⁻¹ * actingElement • element
  have hiterate (exponent : ℕ) :
      actingElement ^ exponent • element = element * displacement ^ exponent := by
    induction exponent with
    | zero => simp
    | succ exponent inductionHypothesis =>
      rw [pow_succ', mul_smul, inductionHypothesis, smul_mul', smul_pow',
        hfixed]
      change actingElement • element * displacement ^ exponent =
        element * displacement ^ (exponent + 1)
      rw [pow_succ']
      simp only [displacement, mul_assoc, mul_inv_cancel_left]
  have hactorPower : displacement ^ Nat.card Actor = 1 := by
    have hequality := hiterate (Nat.card Actor)
    rw [pow_card_eq_one', one_smul] at hequality
    exact mul_left_cancel (hequality.symm.trans (mul_one element).symm)
  have hdisplacement : displacement = 1 :=
    (pow_eq_one_iff_of_coprime hcoprime).mp ⟨pow_card_eq_one', hactorPower⟩
  have hequality := congrArg (fun value : Value => element * value) hdisplacement
  simpa only [displacement, mul_inv_cancel_left, mul_one] using hequality

theorem coprime_action_trivial_of_fixed_displacements
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (hfixed : ∀ actingElement : Actor, ∀ element : Value,
      actingElement • (element⁻¹ * actingElement • element) =
        element⁻¹ * actingElement • element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  intro actingElement element
  exact coprime_element_fixed_of_fixed_displacement hcoprime actingElement element
    (hfixed actingElement element)

theorem coprime_action_trivial_of_normal_self_centralizing_fixed_subgroup
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (fixedGroup : Subgroup Value) (hnormal : fixedGroup.Normal)
    (hselfCentralizing : Subgroup.centralizer (fixedGroup : Set Value) ≤ fixedGroup)
    (hfixed : ∀ actingElement : Actor, ∀ element ∈ fixedGroup,
      actingElement • element = element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  apply coprime_action_trivial_of_fixed_displacements hcoprime
  intro actingElement element
  apply hfixed actingElement
  apply hselfCentralizing
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

theorem class_two_self_centralizing_subgroup_normal
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (fixedGroup : Subgroup Value)
    (hselfCentralizing : Subgroup.centralizer (fixedGroup : Set Value) ≤ fixedGroup) :
    fixedGroup.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
  exact (Subgroup.commutator_mono le_rfl le_top).trans
    (hclassTwo.trans ((Subgroup.center_le_centralizer (fixedGroup : Set Value)).trans
      hselfCentralizing))

theorem class_two_coprime_action_trivial_of_self_centralizing_fixed_subgroup
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (fixedGroup : Subgroup Value)
    (hselfCentralizing : Subgroup.centralizer (fixedGroup : Set Value) ≤ fixedGroup)
    (hfixed : ∀ actingElement : Actor, ∀ element ∈ fixedGroup,
      actingElement • element = element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  exact coprime_action_trivial_of_normal_self_centralizing_fixed_subgroup hcoprime fixedGroup
    (class_two_self_centralizing_subgroup_normal hclassTwo fixedGroup hselfCentralizing)
    hselfCentralizing hfixed

theorem maximal_abelian_subgroup_self_centralizing
    {Value : Type*} [Group Value] (abelianGroup : Subgroup Value)
    (habelian : IsMulCommutative abelianGroup)
    (hmaximal : ∀ overgroup : Subgroup Value, abelianGroup ≤ overgroup →
      IsMulCommutative overgroup → overgroup = abelianGroup) :
    Subgroup.centralizer (abelianGroup : Set Value) ≤ abelianGroup := by
  intro element hcentralizing
  let extendedGroup := Subgroup.closure ((abelianGroup : Set Value) ∪ {element})
  have hpairwise : ((abelianGroup : Set Value) ∪ {element}).Pairwise Commute := by
    intro first hfirst second hsecond _
    rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
    · exact (commute_iff_eq _ _).mpr (congrArg Subtype.val
        (isMulCommutative_iff.mp habelian
          (⟨first, hfirst⟩ : abelianGroup) (⟨second, hsecond⟩ : abelianGroup)))
    · have hequal : second = element := Set.mem_singleton_iff.mp hsecond
      subst second
      exact (commute_iff_eq _ _).mpr
        (Subgroup.mem_centralizer_iff.mp hcentralizing first hfirst)
    · have hequal : first = element := Set.mem_singleton_iff.mp hfirst
      subst first
      exact (commute_iff_eq _ _).mpr
        (Subgroup.mem_centralizer_iff.mp hcentralizing second hsecond).symm
    · have hfirstEqual : first = element := Set.mem_singleton_iff.mp hfirst
      have hsecondEqual : second = element := Set.mem_singleton_iff.mp hsecond
      subst first second
      exact Commute.refl element
  have hextendedAbelian : IsMulCommutative extendedGroup := by
    apply CFSG.subgroup_isMulCommutative_closure
    intro first hfirst second hsecond
    by_cases hequal : first = second
    · rw [hequal]
    · exact (hpairwise hfirst hsecond hequal).eq
  have hcontained : abelianGroup ≤ extendedGroup := by
    intro member hmember
    exact Subgroup.subset_closure (Or.inl hmember)
  have hequal := hmaximal extendedGroup hcontained hextendedAbelian
  have helement : element ∈ extendedGroup := Subgroup.subset_closure (Or.inr rfl)
  exact hequal ▸ helement

theorem class_two_coprime_action_trivial_of_maximal_abelian_fixed_subgroup
    {Actor Value : Type*} [Group Actor] [Finite Actor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value]
    (hcoprime : (Nat.card Value).Coprime (Nat.card Actor))
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (fixedGroup : Subgroup Value) (habelian : IsMulCommutative fixedGroup)
    (hmaximal : ∀ overgroup : Subgroup Value, fixedGroup ≤ overgroup →
      IsMulCommutative overgroup → overgroup = fixedGroup)
    (hfixed : ∀ actingElement : Actor, ∀ element ∈ fixedGroup,
      actingElement • element = element) :
    ∀ actingElement : Actor, ∀ element : Value, actingElement • element = element := by
  exact class_two_coprime_action_trivial_of_self_centralizing_fixed_subgroup
    hcoprime hclassTwo fixedGroup
    (maximal_abelian_subgroup_self_centralizing fixedGroup habelian hmaximal) hfixed

theorem commutative_pGroup_axb_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Finite OtherActor]
    [CommGroup Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  classical
  let : Fintype OtherActor := Fintype.ofFinite OtherActor
  let actorAction := MulDistribMulAction.toMulAut Actor Value
  let otherAction := MulDistribMulAction.toMulAut OtherActor Value
  let : DistribMulAction Actor (Additive Value) := additiveActionOfMulAutHom actorAction
  let : DistribMulAction OtherActor (Additive Value) := additiveActionOfMulAutHom otherAction
  have hresult := abelian_pGroup_axb_lemma (Value := Additive Value)
    prime hprime hactor hvalue (by
      rw [← Nat.card_congr (Additive.ofMul : Value ≃ Additive Value)]
      simpa only [Nat.card_eq_fintype_card] using hcoprime)
    hcommute hcentralizes
  exact hresult

theorem commutative_pGroup_normalized_actor_fixed_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Finite OtherActor]
    [CommGroup Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (normalizingAction : Actor →* MulAut OtherActor)
    (hcompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element) :
    ∀ otherElement : OtherActor, ∀ element : Value, otherElement • element = element := by
  classical
  let : Fintype OtherActor := Fintype.ofFinite OtherActor
  let actorAction := MulDistribMulAction.toMulAut Actor Value
  let otherAction := MulDistribMulAction.toMulAut OtherActor Value
  let : DistribMulAction Actor (Additive Value) := additiveActionOfMulAutHom actorAction
  let : DistribMulAction OtherActor (Additive Value) := additiveActionOfMulAutHom otherAction
  exact abelian_pGroup_normalized_actor_fixed_lemma (Value := Additive Value)
    prime hprime hactor hvalue (by
      rw [← Nat.card_congr (Additive.ofMul : Value ≃ Additive Value)]
      simpa only [Nat.card_eq_fintype_card] using hcoprime)
    normalizingAction hcompatibility hcentralizes

theorem commutative_pGroup_normalized_actor_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Finite OtherActor]
    [CommGroup Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
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
  let : Fintype OtherActor := Fintype.ofFinite OtherActor
  let actorAction := MulDistribMulAction.toMulAut Actor Value
  let otherAction := MulDistribMulAction.toMulAut OtherActor Value
  let : DistribMulAction Actor (Additive Value) := additiveActionOfMulAutHom actorAction
  let : DistribMulAction OtherActor (Additive Value) := additiveActionOfMulAutHom otherAction
  exact abelian_pGroup_normalized_actor_fixed_order_prime_lemma (Value := Additive Value)
    prime hprime hactor hvalue (by
      rw [← Nat.card_congr (Additive.ofMul : Value ≃ Additive Value)]
      simpa only [Nat.card_eq_fintype_card] using hcoprime)
    normalizingAction hcompatibility hcentralizes

@[expose] def characteristicQuotientActionHom
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    (hcharacteristic : invariantGroup.Characteristic) :
    Actor →* MulAut (Value ⧸ invariantGroup) where
  toFun actingElement := QuotientGroup.congr invariantGroup invariantGroup
    (action actingElement)
    (by
      rw [← MulEquiv.toMonoidHom_eq_coe]
      exact Subgroup.characteristic_iff_map_eq.mp hcharacteristic (action actingElement))
  map_one' := by
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    simp only [QuotientGroup.congr_mk', map_one, MulAut.one_apply]
  map_mul' := by
    intro first second
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    simp only [MulAut.mul_apply]
    rw [QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk', map_mul]
    rfl

theorem pGroup_axb_lemma
    {Actor OtherActor : Type*} {Value : Type u}
    [Group Actor] [Group OtherActor] [Finite OtherActor] [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (hvalue : IsPGroup prime Value)
    (hcoprime : (Nat.card Value).Coprime (Nat.card OtherActor))
    (hcommute : ∀ actingElement : Actor, ∀ otherElement : OtherActor, ∀ element : Value,
      actingElement • otherElement • element = otherElement • actingElement • element)
    (hcentralizes : ∀ element : Value, (∀ actingElement : Actor, actingElement • element = element) →
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
          otherAction otherElement (actorAction actingElement element)) →
      (∀ element : ValueGroup,
        (∀ actingElement : Actor, actorAction actingElement element = element) →
        ∀ otherElement : OtherActor, otherAction otherElement element = element) →
      ∀ otherElement : OtherActor, ∀ element : ValueGroup,
        otherAction otherElement element = element := by
    intro cardinal
    induction cardinal using Nat.strong_induction_on with
    | h cardinal inductionHypothesis =>
      intro ValueGroup groupInstance finiteInstance hcardinal actorAction otherAction
        hgroup hgroupCoprime hactionsCommute hfixedCentralized
      let : MulDistribMulAction Actor ValueGroup :=
        multiplicativeActionOfMulAutHom actorAction
      let : MulDistribMulAction OtherActor ValueGroup :=
        multiplicativeActionOfMulAutHom otherAction
      let centralGroup := Subgroup.center ValueGroup
      have hcharacteristic : centralGroup.Characteristic := Subgroup.centerCharacteristic
      let : CommGroup centralGroup := {
        centralGroup.toGroup with
        mul_comm := by
          intro first second
          apply Subtype.ext
          exact Subgroup.mem_center_iff.mp second.property first }
      let centerActorAction := characteristicActionHom actorAction centralGroup hcharacteristic
      let centerOtherAction := characteristicActionHom otherAction centralGroup hcharacteristic
      let : MulDistribMulAction Actor centralGroup :=
        multiplicativeActionOfMulAutHom centerActorAction
      let : MulDistribMulAction OtherActor centralGroup :=
        multiplicativeActionOfMulAutHom centerOtherAction
      have hcenterFixed : ∀ otherElement : OtherActor, ∀ element : centralGroup,
          centerOtherAction otherElement element = element := by
        apply commutative_pGroup_axb_lemma prime hprime hactor
          (hgroup.to_subgroup centralGroup)
          (hgroupCoprime.of_dvd_left centralGroup.card_subgroup_dvd_card)
        · intro actingElement otherElement element
          apply Subtype.ext
          exact hactionsCommute actingElement otherElement element
        · intro element hfixed otherElement
          apply Subtype.ext
          exact hfixedCentralized element
            (fun actingElement => congrArg Subtype.val (hfixed actingElement)) otherElement
      have hcenterFixedAmbient (otherElement : OtherActor) (element : ValueGroup)
          (helement : element ∈ centralGroup) : otherAction otherElement element = element :=
        congrArg Subtype.val (hcenterFixed otherElement ⟨element, helement⟩)
      by_cases hcenterTop : centralGroup = ⊤
      · intro otherElement element
        exact hcenterFixedAmbient otherElement element (hcenterTop ▸ Subgroup.mem_top element)
      · have hnontrivial : Nontrivial ValueGroup := by
          by_contra htrivial
          let : Subsingleton ValueGroup := not_nontrivial_iff_subsingleton.mp htrivial
          apply hcenterTop
          apply top_unique
          intro element _
          exact Subgroup.mem_center_iff.mpr (fun other => Subsingleton.elim _ _)
        let : Nontrivial ValueGroup := hnontrivial
        let : Nontrivial centralGroup := hgroup.center_nontrivial
        have hcenterCard : 1 < Nat.card centralGroup := by
          have hpositive : 0 < Nat.card centralGroup := Nat.card_pos
          have hne : Nat.card centralGroup ≠ 1 := by
            intro hequal
            have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hequal).1
            exact not_subsingleton centralGroup hsubsingleton
          omega
        have hquotientCard : Nat.card (ValueGroup ⧸ centralGroup) < cardinal := by
          have hproduct := centralGroup.index_mul_card
          rw [centralGroup.index_eq_card] at hproduct
          have hpositive : 0 < Nat.card (ValueGroup ⧸ centralGroup) := Nat.card_pos
          have hstrict : Nat.card (ValueGroup ⧸ centralGroup) <
              Nat.card (ValueGroup ⧸ centralGroup) * Nat.card centralGroup := by
            nlinarith
          rwa [hproduct, hcardinal] at hstrict
        let quotientActorAction :=
          characteristicQuotientActionHom actorAction centralGroup hcharacteristic
        let quotientOtherAction :=
          characteristicQuotientActionHom otherAction centralGroup hcharacteristic
        have hquotientApply (groupAction : Actor →* MulAut ValueGroup)
            (actingElement : Actor) (element : ValueGroup) :
            characteristicQuotientActionHom groupAction centralGroup hcharacteristic
                actingElement ((QuotientGroup.mk' centralGroup) element) =
              (QuotientGroup.mk' centralGroup) (groupAction actingElement element) := by
          dsimp only [characteristicQuotientActionHom, MonoidHom.coe_mk, OneHom.coe_mk]
          rw [QuotientGroup.congr_mk']
        have hquotientOtherApply (otherElement : OtherActor) (element : ValueGroup) :
            quotientOtherAction otherElement ((QuotientGroup.mk' centralGroup) element) =
              (QuotientGroup.mk' centralGroup) (otherAction otherElement element) := by
          dsimp only [quotientOtherAction, characteristicQuotientActionHom,
            MonoidHom.coe_mk, OneHom.coe_mk]
          rw [QuotientGroup.congr_mk']
        have hquotientFixed : ∀ otherElement : OtherActor,
            ∀ element : ValueGroup ⧸ centralGroup,
            quotientOtherAction otherElement element = element := by
          apply inductionHypothesis (Nat.card (ValueGroup ⧸ centralGroup)) hquotientCard
            (ValueGroup ⧸ centralGroup) rfl quotientActorAction quotientOtherAction
          · exact hgroup.of_surjective (QuotientGroup.mk' centralGroup)
              (QuotientGroup.mk'_surjective centralGroup)
          · exact hgroupCoprime.of_dvd_left centralGroup.card_quotient_dvd_card
          · intro actingElement otherElement element
            obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective centralGroup element
            rw [hquotientOtherApply, hquotientApply, hquotientApply, hquotientOtherApply]
            exact congrArg (QuotientGroup.mk' centralGroup)
              (hactionsCommute actingElement otherElement preimage)
          · intro element hfixed otherElement
            obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective centralGroup element
            have hdisplacements (actingElement : Actor) :
                preimage⁻¹ * actorAction actingElement preimage ∈ centralGroup := by
              apply QuotientGroup.eq.mp
              exact (hquotientApply actorAction actingElement preimage).symm.trans
                (hfixed actingElement) |>.symm
            have hotherDisplacementFixed : ∀ actingElement : Actor,
                actorAction actingElement (preimage⁻¹ * otherAction otherElement preimage) =
                  preimage⁻¹ * otherAction otherElement preimage := by
              intro actingElement
              let displacement := preimage⁻¹ * actorAction actingElement preimage
              have hdisplacement := hdisplacements actingElement
              have hactorPreimage : actorAction actingElement preimage = preimage * displacement := by
                simp only [displacement, mul_inv_cancel_left]
              have hdisplacementCentral := Subgroup.mem_center_iff.mp hdisplacement
                (preimage⁻¹ * otherAction otherElement preimage)
              change (preimage⁻¹ * otherAction otherElement preimage) * displacement =
                displacement * (preimage⁻¹ * otherAction otherElement preimage)
                at hdisplacementCentral
              rw [map_mul, map_inv, hactionsCommute, hactorPreimage, map_mul,
                hcenterFixedAmbient otherElement displacement hdisplacement, mul_inv_rev]
              simpa only [mul_assoc, inv_mul_cancel_left] using
                congrArg (fun value : ValueGroup => displacement⁻¹ * value)
                  hdisplacementCentral
            have hotherFixedDisplacement :=
              hfixedCentralized (preimage⁻¹ * otherAction otherElement preimage)
                hotherDisplacementFixed otherElement
            have hpreimageFixed := coprime_element_fixed_of_fixed_displacement
              hgroupCoprime otherElement preimage hotherFixedDisplacement
            exact (hquotientOtherApply otherElement preimage).trans
              (congrArg (QuotientGroup.mk' centralGroup) hpreimageFixed)
        apply coprime_action_trivial_of_fixed_displacements hgroupCoprime
        intro otherElement element
        have hdisplacement : element⁻¹ * otherAction otherElement element ∈ centralGroup := by
          apply QuotientGroup.eq.mp
          exact ((hquotientOtherApply otherElement element).symm.trans
            (hquotientFixed otherElement ((QuotientGroup.mk' centralGroup) element))).symm
        exact hcenterFixedAmbient otherElement _ hdisplacement
  exact inductiveClaim (Nat.card Value) Value rfl
    (MulDistribMulAction.toMulAut Actor Value) (MulDistribMulAction.toMulAut OtherActor Value)
    hvalue hcoprime hcommute hcentralizes

theorem ambient_subgroup_axb_centralizer_le
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime)
    (actingGroup otherGroup valueGroup : Subgroup G)
    (hactor : IsPGroup prime actingGroup) (hvalue : IsPGroup prime valueGroup)
    (hcoprime : (Nat.card valueGroup).Coprime (Nat.card otherGroup))
    (hactorNormalizes : actingGroup ≤ Subgroup.normalizer (valueGroup : Set G))
    (hotherNormalizes : otherGroup ≤ Subgroup.normalizer (valueGroup : Set G))
    (hcommute : otherGroup ≤ Subgroup.centralizer (actingGroup : Set G))
    (hcentralizes : otherGroup ≤ Subgroup.centralizer
      ((valueGroup ⊓ Subgroup.centralizer (actingGroup : Set G) : Subgroup G) : Set G)) :
    otherGroup ≤ Subgroup.centralizer (valueGroup : Set G) := by
  let actorAction := ambientSubgroupActionHom actingGroup valueGroup hactorNormalizes
  let otherAction := ambientSubgroupActionHom otherGroup valueGroup hotherNormalizes
  let : MulDistribMulAction actingGroup valueGroup :=
    multiplicativeActionOfMulAutHom actorAction
  let : MulDistribMulAction otherGroup valueGroup :=
    multiplicativeActionOfMulAutHom otherAction
  have hactionsCommute : ∀ actingElement : actingGroup, ∀ otherElement : otherGroup,
      ∀ element : valueGroup,
      actingElement • otherElement • element = otherElement • actingElement • element := by
    intro actingElement otherElement element
    apply Subtype.ext
    have hcommuting := Subgroup.mem_centralizer_iff.mp
      (hcommute otherElement.property) actingElement actingElement.property
    have hconj := congrArg (fun automorphism : MulAut G => automorphism (element : G))
      (congrArg MulAut.conj hcommuting)
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at hconj
    change ((actorAction actingElement (otherAction otherElement element)) : G) =
      ((otherAction otherElement (actorAction actingElement element)) : G)
    simpa only [actorAction, otherAction, ambientSubgroupActionHom_apply_coe,
      MulAut.conj_apply] using hconj
  have hfixedCentralized : ∀ element : valueGroup,
      (∀ actingElement : actingGroup, actingElement • element = element) →
      ∀ otherElement : otherGroup, otherElement • element = element := by
    intro element hfixed otherElement
    have helementCentralizes : (element : G) ∈ Subgroup.centralizer (actingGroup : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro actingElement hactingElement
      have hequality := congrArg Subtype.val (hfixed ⟨actingElement, hactingElement⟩)
      change actingElement * (element : G) * actingElement⁻¹ = element at hequality
      have hcancel := congrArg (fun value : G => value * actingElement) hequality
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    have hcommuting := Subgroup.mem_centralizer_iff.mp
      (hcentralizes otherElement.property) element ⟨element.property, helementCentralizes⟩
    apply Subtype.ext
    change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ = element
    rw [← hcommuting, mul_inv_cancel_right]
  have hresult := pGroup_axb_lemma prime hprime hactor hvalue hcoprime
    hactionsCommute hfixedCentralized
  intro otherElement hotherElement
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  have hequality := congrArg Subtype.val
    (hresult ⟨otherElement, hotherElement⟩ ⟨element, helement⟩)
  change otherElement * element * otherElement⁻¹ = element at hequality
  have hcancel := congrArg (fun value : G => value * otherElement) hequality
  have hequal : otherElement * element = element * otherElement := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
  exact hequal.symm

theorem charTwo_odd_pGroup_centralizing_core_fixed_subgroup_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (actingGroup : Subgroup G) (hactor : IsPGroup 2 actingGroup)
    (hactorLe : actingGroup ≤ localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (otherGroup : Subgroup G) (hother : IsPGroup prime otherGroup)
    (hotherLe : otherGroup ≤ localGroup)
    (hcommute : otherGroup ≤ Subgroup.centralizer (actingGroup : Set G))
    (hcentralizes : otherGroup ≤ Subgroup.centralizer
      ((pCoreOf 2 localGroup ⊓ Subgroup.centralizer (actingGroup : Set G) : Subgroup G) : Set G)) :
    otherGroup = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨coreExponent, hcoreCard⟩ :=
    IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 localGroup)
  obtain ⟨otherExponent, hotherCard⟩ := IsPGroup.iff_card.mp hother
  have hcoprime : (Nat.card (pCoreOf 2 localGroup)).Coprime (Nat.card otherGroup) := by
    rw [hcoreCard, hotherCard]
    exact ((Nat.coprime_primes Nat.prime_two hprime).mpr hodd.symm).pow _ _
  apply charTwo_odd_pGroup_centralizing_core_eq_bot hchar localGroup hlocal
    prime hprime hodd otherGroup hother hotherLe
  exact ambient_subgroup_axb_centralizer_le 2 Nat.prime_two actingGroup otherGroup
    (pCoreOf 2 localGroup) hactor (pCoreOf_isPGroup 2 localGroup) hcoprime
    (hactorLe.trans (localGroup_le_normalizer_pCoreOf 2 localGroup))
    (hotherLe.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)) hcommute hcentralizes

theorem normalizer_le_normalizer_centralizer
    {G : Type*} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (subgroup : Set G) : Set G) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (subgroup : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (subgroup : Set G))

theorem common_normalizer_le_normalizer_inf
    {G : Type*} [Group G] (actingGroup firstGroup secondGroup : Subgroup G)
    (hfirst : actingGroup ≤ Subgroup.normalizer (firstGroup : Set G))
    (hsecond : actingGroup ≤ Subgroup.normalizer (secondGroup : Set G)) :
    actingGroup ≤ Subgroup.normalizer ((firstGroup ⊓ secondGroup : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actingElement hactingElement element helement
  exact ⟨(Subgroup.le_normalizer_iff.mp hfirst actingElement hactingElement element helement.1),
    (Subgroup.le_normalizer_iff.mp hsecond actingElement hactingElement element helement.2)⟩

theorem local_core_fixed_subgroup_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ)
    (overgroup actingGroup localGroup : Subgroup G)
    (hlocalLe : localGroup ≤ overgroup)
    (hactorNormalizes : localGroup ≤ Subgroup.normalizer (actingGroup : Set G)) :
    pCoreOf prime overgroup ⊓ Subgroup.centralizer (actingGroup : Set G) ⊓ localGroup ≤
      pCoreOf prime localGroup := by
  let fixedGroup := pCoreOf prime overgroup ⊓ Subgroup.centralizer (actingGroup : Set G)
  have hnormalizes : localGroup ≤ Subgroup.normalizer (fixedGroup : Set G) :=
    common_normalizer_le_normalizer_inf localGroup (pCoreOf prime overgroup)
      (Subgroup.centralizer (actingGroup : Set G))
      (hlocalLe.trans (localGroup_le_normalizer_pCoreOf prime overgroup))
      (hactorNormalizes.trans (normalizer_le_normalizer_centralizer actingGroup))
  apply normal_pGroup_le_pCoreOf prime (fixedGroup ⊓ localGroup) localGroup inf_le_right
  · apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    exact common_normalizer_le_normalizer_inf localGroup fixedGroup localGroup
      hnormalizes Subgroup.le_normalizer
  · exact (pCoreOf_isPGroup prime overgroup).of_injective
      (Subgroup.inclusion (show fixedGroup ⊓ localGroup ≤ pCoreOf prime overgroup from
        inf_le_left.trans inf_le_left)) (Subgroup.inclusion_injective _)

theorem charTwo_internal_normalizer_core_centralizer_le
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (overgroup : Subgroup G) (hlocal : IsTwoLocal overgroup)
    (actingGroup : Subgroup G) (hactor : IsPGroup 2 actingGroup)
    (hactorLe : actingGroup ≤ overgroup) :
    let localGroup := overgroup ⊓ Subgroup.normalizer (actingGroup : Set G)
    localGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) ≤
      pCoreOf 2 localGroup := by
  classical
  let localGroup := overgroup ⊓ Subgroup.normalizer (actingGroup : Set G)
  let centralGroup := localGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G)
  change centralGroup ≤ pCoreOf 2 localGroup
  have hlocalLe : localGroup ≤ overgroup := inf_le_left
  have hactorNormalizes : localGroup ≤ Subgroup.normalizer (actingGroup : Set G) := inf_le_right
  have hactorLocal : actingGroup ≤ localGroup :=
    le_inf hactorLe Subgroup.le_normalizer
  have hactorCore : actingGroup ≤ pCoreOf 2 localGroup := by
    apply normal_pGroup_le_pCoreOf 2 actingGroup localGroup hactorLocal
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hactorLocal).mpr hactorNormalizes) hactor
  have hfixedLe : pCoreOf 2 overgroup ⊓ Subgroup.centralizer (actingGroup : Set G) ≤
      localGroup := by
    apply le_inf
    · exact inf_le_left.trans (pCoreOf_le 2 overgroup)
    · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (actingGroup : Set G))
  have hfixedCore : pCoreOf 2 overgroup ⊓ Subgroup.centralizer (actingGroup : Set G) ≤
      pCoreOf 2 localGroup := by
    intro element helement
    exact local_core_fixed_subgroup_le 2 overgroup actingGroup localGroup hlocalLe
      hactorNormalizes ⟨helement, hfixedLe helement⟩
  have hcentralPGroup : IsPGroup 2 centralGroup := by
    apply IsPGroup.of_card (n := (Nat.card centralGroup).primeFactorsList.length)
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro prime hprime hdivisibility
    by_contra hodd
    let : Fact prime.Prime := ⟨hprime⟩
    obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' prime hdivisibility
    let otherGroup := Subgroup.zpowers (element : G)
    have hother : IsPGroup prime otherGroup := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, horder, pow_one]
    have hotherLocal : otherGroup ≤ localGroup :=
      Subgroup.zpowers_le.mpr element.property.1
    have hotherCentral : otherGroup ≤ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) :=
      Subgroup.zpowers_le.mpr element.property.2
    have hotherBot : otherGroup = ⊥ :=
      charTwo_odd_pGroup_centralizing_core_fixed_subgroup_eq_bot hchar overgroup hlocal
        actingGroup hactor hactorLe prime hprime hodd otherGroup hother
        (hotherLocal.trans hlocalLe)
        (hotherCentral.trans (Subgroup.centralizer_le hactorCore))
        (hotherCentral.trans (Subgroup.centralizer_le hfixedCore))
    have helementOne : (element : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hotherBot]
      exact Subgroup.mem_zpowers _
    have horderOne : orderOf element = 1 := by
      rw [← Subgroup.orderOf_coe element, helementOne, orderOf_one]
    exact hprime.ne_one (horder.symm.trans horderOne)
  have hcentralNormalizes : localGroup ≤
      Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 localGroup : Set G) : Set G) :=
    (localGroup_le_normalizer_pCoreOf 2 localGroup).trans
      (normalizer_le_normalizer_centralizer (pCoreOf 2 localGroup))
  exact normal_pGroup_le_pCoreOf 2 centralGroup localGroup inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (common_normalizer_le_normalizer_inf localGroup localGroup
        (Subgroup.centralizer (pCoreOf 2 localGroup : Set G))
        Subgroup.le_normalizer hcentralNormalizes)) hcentralPGroup

theorem pCore_map_mulEquiv_le
    {Source Target : Type*} [Group Source] [Group Target]
    (prime : ℕ) (equivalence : Source ≃* Target) :
    (pCore prime Source).map equivalence.toMonoidHom ≤ pCore prime Target := by
  exact normal_pGroup_le_pCore prime _
    ((pCore_normal prime).map equivalence.toMonoidHom equivalence.surjective)
    ((pCore_isPGroup prime).map equivalence.toMonoidHom)

theorem pCore_map_mulEquiv
    {Source Target : Type*} [Group Source] [Group Target]
    (prime : ℕ) (equivalence : Source ≃* Target) :
    (pCore prime Source).map equivalence.toMonoidHom = pCore prime Target := by
  apply le_antisymm (pCore_map_mulEquiv_le prime equivalence)
  have hreverse := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (pCore_map_mulEquiv_le prime equivalence.symm)
  have hcomp : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id Target := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at hreverse

theorem pCoreOf_map_subtype
    {G : Type*} [Group G] (prime : ℕ) (overgroup : Subgroup G)
    (localGroup : Subgroup overgroup) :
    (pCoreOf prime localGroup).map overgroup.subtype =
      pCoreOf prime (localGroup.map overgroup.subtype) := by
  let equivalence := localGroup.equivMapOfInjective overgroup.subtype
    overgroup.subtype_injective
  have hhom : (localGroup.map overgroup.subtype).subtype.comp equivalence.toMonoidHom =
      overgroup.subtype.comp localGroup.subtype := by
    ext element
    rfl
  unfold pCoreOf
  rw [← pCore_map_mulEquiv prime equivalence, Subgroup.map_map, Subgroup.map_map, hhom]

theorem charTwo_twoLocal_isCharTwoType
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (overgroup : Subgroup G) (hlocal : IsTwoLocal overgroup) :
    IsCharTwoType overgroup := by
  intro internalLocal hinternalLocal
  obtain ⟨internalActor, _, hactor, hnormalizer⟩ := hinternalLocal
  let actingGroup := internalActor.map overgroup.subtype
  let localGroup := internalLocal.map overgroup.subtype
  have hactorLe : actingGroup ≤ overgroup := Subgroup.map_subtype_le _
  have hactorGroup : IsPGroup 2 actingGroup := hactor.map overgroup.subtype
  have hactorComap : actingGroup.comap overgroup.subtype = internalActor :=
    Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective internalActor
  have hlocalMap : localGroup = overgroup ⊓ Subgroup.normalizer (actingGroup : Set G) := by
    have hcomap : (Subgroup.normalizer (actingGroup : Set G)).comap overgroup.subtype =
        internalLocal := by
      rw [Subgroup.comap_normalizer_eq_of_le_range
        (hactorLe.trans (le_of_eq overgroup.subtype_range.symm)), hactorComap, ← hnormalizer]
    have hmapped := congrArg (fun subgroup : Subgroup overgroup => subgroup.map overgroup.subtype)
      hcomap
    change ((Subgroup.normalizer (actingGroup : Set G)).subgroupOf overgroup).map
      overgroup.subtype = localGroup at hmapped
    rw [Subgroup.subgroupOf_map_subtype] at hmapped
    exact hmapped.symm.trans (inf_comm _ _)
  have hbound : localGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) ≤
      pCoreOf 2 localGroup := by
    rw [hlocalMap]
    exact charTwo_internal_normalizer_core_centralizer_le hchar overgroup hlocal
      actingGroup hactorGroup hactorLe
  intro element helement
  have hlocalElement : (element : G) ∈ localGroup :=
    Subgroup.mem_map_of_mem overgroup.subtype helement.1
  have hcentralElement : (element : G) ∈ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro coreElement hcoreElement
    rw [← pCoreOf_map_subtype 2 overgroup internalLocal] at hcoreElement
    obtain ⟨internalCoreElement, hinternalCore, rfl⟩ := hcoreElement
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp helement.2 internalCoreElement hinternalCore)
  have hcoreElement := hbound ⟨hlocalElement, hcentralElement⟩
  rw [← pCoreOf_map_subtype 2 overgroup internalLocal] at hcoreElement
  obtain ⟨internalCoreElement, hinternalCore, hequal⟩ := hcoreElement
  exact overgroup.subtype_injective hequal ▸ hinternalCore

theorem abelian_normal_core_signalizer_eq_bot
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (valueGroup : Subgroup G)
    (hnormal : valueGroup.Normal) (habelian : IsMulCommutative valueGroup)
    (hvalue : IsPGroup prime valueGroup)
    (hconstraint : Subgroup.centralizer (valueGroup : Set G) ≤ valueGroup)
    (actingGroup signalizer : Subgroup G) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) : signalizer = ⊥ := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : valueGroup.Normal := hnormal
  let : CommGroup valueGroup := {
    valueGroup.toGroup with
    mul_comm := by
      intro first second
      exact isMulCommutative_iff.mp habelian first second }
  have hcoprime : (Nat.card valueGroup).Coprime (Nat.card signalizer) := by
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hvalue
    rw [hcard]
    exact hsignalizer.pow_left exponent
  have hdisjoint : Disjoint valueGroup signalizer :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  let actorAction := ambientSubgroupActionHom actingGroup valueGroup
    (show actingGroup ≤ Subgroup.normalizer (valueGroup : Set G) by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  let signalizerAction := ambientSubgroupActionHom signalizer valueGroup
    (show signalizer ≤ Subgroup.normalizer (valueGroup : Set G) by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  let normalizingAction := ambientSubgroupActionHom actingGroup signalizer hinvariant
  let : MulDistribMulAction actingGroup valueGroup :=
    multiplicativeActionOfMulAutHom actorAction
  let : MulDistribMulAction signalizer valueGroup :=
    multiplicativeActionOfMulAutHom signalizerAction
  have hcompatibility : ∀ actingElement : actingGroup, ∀ otherElement : signalizer,
      ∀ element : valueGroup,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element := by
    intro actingElement otherElement element
    apply Subtype.ext
    change (actorAction actingElement (signalizerAction otherElement element) : G) =
      (signalizerAction (normalizingAction actingElement otherElement)
        (actorAction actingElement element) : G)
    simp only [actorAction, signalizerAction, normalizingAction,
      ambientSubgroupActionHom_apply_coe]
    group
  have hfixedCentralized : ∀ element : valueGroup,
      element ^ prime = 1 →
      (∀ actingElement : actingGroup, actingElement • element = element) →
      ∀ otherElement : signalizer, otherElement • element = element := by
    intro element hpower hfixed otherElement
    have helementCentralizes : (element : G) ∈ Subgroup.centralizer (actingGroup : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro actingElement hactingElement
      have hequality := congrArg Subtype.val (hfixed ⟨actingElement, hactingElement⟩)
      change actingElement * (element : G) * actingElement⁻¹ = element at hequality
      have hcancel := congrArg (fun value : G => value * actingElement) hequality
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    have helementActor : (element : G) ∈ actingGroup := by
      by_cases helementOne : (element : G) = 1
      · exact helementOne ▸ actingGroup.one_mem
      · exact hcontains element helementCentralizes
          (orderOf_eq_prime (congrArg Subtype.val hpower) helementOne)
    have hcommutator : (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
        (element : G)⁻¹ ∈ valueGroup ⊓ signalizer := by
      constructor
      · exact valueGroup.mul_mem (hnormal.conj_mem element element.property otherElement)
          (valueGroup.inv_mem element.property)
      · have hconjugate := Subgroup.le_normalizer_iff.mp hinvariant element helementActor
          (otherElement : G)⁻¹ (signalizer.inv_mem otherElement.property)
        have hproduct := signalizer.mul_mem otherElement.property hconjugate
        change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
          (element : G)⁻¹ ∈ signalizer
        simpa only [mul_assoc] using hproduct
    have hcommutatorOne : (otherElement : G) * (element : G) * (otherElement : G)⁻¹ *
        (element : G)⁻¹ = 1 := by
      rw [hdisjoint.eq_bot] at hcommutator
      exact Subgroup.mem_bot.mp hcommutator
    apply Subtype.ext
    change (otherElement : G) * (element : G) * (otherElement : G)⁻¹ = element
    have hcancel := congrArg (fun value : G => value * (element : G)) hcommutatorOne
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hcancel
  have hresult := commutative_pGroup_normalized_actor_fixed_order_prime_lemma prime hprime hactor hvalue
    hcoprime normalizingAction hcompatibility hfixedCentralized
  have hcentralizes : signalizer ≤ Subgroup.centralizer (valueGroup : Set G) := by
    intro otherElement hotherElement
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    have hequality := congrArg Subtype.val
      (hresult ⟨otherElement, hotherElement⟩ ⟨element, helement⟩)
    change otherElement * element * otherElement⁻¹ = element at hequality
    have hcancel := congrArg (fun value : G => value * otherElement) hequality
    have hequal : otherElement * element = element * otherElement := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
    exact hequal.symm
  have hcontained := hcentralizes.trans hconstraint
  apply le_bot_iff.mp
  intro element helement
  rw [← hdisjoint.eq_bot]
  exact ⟨hcontained helement, helement⟩

theorem elementary_normal_core_signalizer_eq_bot
    {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (valueGroup : Subgroup G)
    (hnormal : valueGroup.Normal) (helementary : IsElemAbelian prime valueGroup)
    (hconstraint : Subgroup.centralizer (valueGroup : Set G) ≤ valueGroup)
    (actingGroup signalizer : Subgroup G) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set G))
    (hcontains : ∀ element : G,
      element ∈ Subgroup.centralizer (actingGroup : Set G) →
      orderOf element = prime → element ∈ actingGroup) : signalizer = ⊥ := by
  exact abelian_normal_core_signalizer_eq_bot prime hprime valueGroup hnormal helementary.1
    (elementary_isPGroup prime valueGroup helementary) hconstraint actingGroup signalizer
    hactor hsignalizer hinvariant hcontains

theorem coprime_quotient_preserves_order_prime_centralizer_condition
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target]
    (prime : ℕ) (hprime : prime.Prime) (actingGroup : Subgroup Source)
    (hactor : IsPGroup prime actingGroup)
    (homomorphism : Source →* Target) (hsurjective : Function.Surjective homomorphism)
    (hcoprime : prime.Coprime (Nat.card homomorphism.ker))
    (hcontains : ∀ element : Source,
      element ∈ Subgroup.centralizer (actingGroup : Set Source) →
      orderOf element = prime → element ∈ actingGroup) :
    ∀ element : Target,
      element ∈ Subgroup.centralizer (actingGroup.map homomorphism : Set Target) →
      orderOf element = prime → element ∈ actingGroup.map homomorphism := by
  let : Fact prime.Prime := ⟨hprime⟩
  let sourceAction := MulAut.conj.comp actingGroup.subtype
  let targetAction := MulAut.conj.comp (homomorphism.comp actingGroup.subtype)
  let : MulDistribMulAction actingGroup Source := multiplicativeActionOfMulAutHom sourceAction
  let : MulDistribMulAction actingGroup Target := multiplicativeActionOfMulAutHom targetAction
  let : MulAction actingGroup Source :=
    (multiplicativeActionOfMulAutHom sourceAction).toMulAction
  let : MulAction actingGroup Target :=
    (multiplicativeActionOfMulAutHom targetAction).toMulAction
  intro element hcentralizes horder
  have hfixed : ∀ actingElement : actingGroup, actingElement • element = element := by
    intro actingElement
    change homomorphism actingElement * element * (homomorphism actingElement)⁻¹ = element
    have hcommute := Subgroup.mem_centralizer_iff.mp hcentralizes (homomorphism actingElement)
      (Subgroup.mem_map_of_mem homomorphism actingElement.property)
    rw [hcommute, mul_inv_cancel_right]
  have hequivariant : ∀ actingElement : actingGroup, ∀ sourceElement : Source,
      homomorphism (actingElement • sourceElement) =
        actingElement • homomorphism sourceElement := by
    intro actingElement sourceElement
    change homomorphism ((actingElement : Source) * sourceElement * (actingElement : Source)⁻¹) =
      homomorphism actingElement * homomorphism sourceElement * (homomorphism actingElement)⁻¹
    rw [map_mul, map_mul, map_inv]
  obtain ⟨preimage, hpreimage, hpreimageFixed⟩ := coprime_pGroup_fixed_lift prime hprime hactor
    homomorphism hsurjective hequivariant hcoprime element hfixed
  let primeElement := preimage ^ Nat.card homomorphism.ker
  have hprimePower : primeElement ^ prime = 1 := by
    have hkernel : preimage ^ prime ∈ homomorphism.ker := by
      rw [MonoidHom.mem_ker, map_pow, hpreimage, ← horder]
      exact pow_orderOf_eq_one element
    have hpower : (⟨preimage ^ prime, hkernel⟩ : homomorphism.ker) ^
        Nat.card homomorphism.ker = 1 := pow_card_eq_one'
    have hambient := congrArg Subtype.val hpower
    simpa only [primeElement, Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul, Nat.mul_comm]
      using hambient
  have hprimeImage : homomorphism primeElement = element ^ Nat.card homomorphism.ker := by
    dsimp only [primeElement]
    rw [map_pow, hpreimage]
  have hprimeNontrivial : primeElement ≠ 1 := by
    intro hequal
    have hpower : element ^ Nat.card homomorphism.ker = 1 := by
      rw [← hprimeImage, hequal, map_one]
    have hpowerPrime : element ^ prime = 1 := by
      rw [← horder]
      exact pow_orderOf_eq_one element
    have helementOne := (pow_eq_one_iff_of_coprime hcoprime).mp ⟨hpowerPrime, hpower⟩
    rw [helementOne, orderOf_one] at horder
    exact hprime.ne_one horder.symm
  have hprimeCentralizes : primeElement ∈ Subgroup.centralizer (actingGroup : Set Source) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro actingElement hactingElement
    have hfixedPreimage := hpreimageFixed (⟨actingElement, hactingElement⟩ : actingGroup)
    have hfixedPower : (⟨actingElement, hactingElement⟩ : actingGroup) • primeElement =
        primeElement := by
      dsimp only [primeElement]
      rw [smul_pow', hfixedPreimage]
    change actingElement * primeElement * actingElement⁻¹ = primeElement at hfixedPower
    have hcancel := congrArg (fun value : Source => value * actingElement) hfixedPower
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcancel
  have hprimeActor := hcontains primeElement hprimeCentralizes
    (orderOf_eq_prime hprimePower hprimeNontrivial)
  have hpowerActor : element ^ Nat.card homomorphism.ker ∈ actingGroup.map homomorphism := by
    rw [← hprimeImage]
    exact Subgroup.mem_map_of_mem homomorphism hprimeActor
  apply (Subgroup.zpowers_le.mpr hpowerActor)
  apply mem_zpowers_pow_iff.mpr
  rw [horder]
  exact hcoprime.symm

theorem abelian_quotient_core_signalizer_le_kernel
    {Source Target : Type*} [Group Source] [Finite Source] [Group Target] [Finite Target]
    (prime : ℕ) (hprime : prime.Prime)
    (homomorphism : Source →* Target) (hsurjective : Function.Surjective homomorphism)
    (hkernel : prime.Coprime (Nat.card homomorphism.ker))
    (valueGroup : Subgroup Target) (hnormal : valueGroup.Normal)
    (habelian : IsMulCommutative valueGroup) (hvalue : IsPGroup prime valueGroup)
    (hconstraint : Subgroup.centralizer (valueGroup : Set Target) ≤ valueGroup)
    (actingGroup signalizer : Subgroup Source) (hactor : IsPGroup prime actingGroup)
    (hsignalizer : prime.Coprime (Nat.card signalizer))
    (hinvariant : actingGroup ≤ Subgroup.normalizer (signalizer : Set Source))
    (hcontains : ∀ element : Source,
      element ∈ Subgroup.centralizer (actingGroup : Set Source) →
      orderOf element = prime → element ∈ actingGroup) :
    signalizer ≤ homomorphism.ker := by
  have himageCoprime : prime.Coprime (Nat.card (signalizer.map homomorphism)) := by
    exact hsignalizer.of_dvd_right
      (CFSG.card_dvd_of_surjective
        (homomorphism.subgroupMap signalizer) (homomorphism.subgroupMap_surjective signalizer))
  have himageInvariant : actingGroup.map homomorphism ≤
      Subgroup.normalizer (signalizer.map homomorphism : Set Target) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actingElement ⟨actingPreimage, hactingPreimage, rfl⟩
      element ⟨preimage, hpreimage, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem homomorphism
      (Subgroup.le_normalizer_iff.mp hinvariant actingPreimage hactingPreimage preimage hpreimage)
  have htrivial := abelian_normal_core_signalizer_eq_bot prime hprime valueGroup
    hnormal habelian hvalue hconstraint (actingGroup.map homomorphism)
    (signalizer.map homomorphism) (hactor.map homomorphism) himageCoprime himageInvariant
    (coprime_quotient_preserves_order_prime_centralizer_condition prime hprime
      actingGroup hactor homomorphism hsurjective hkernel hcontains)
  intro element helement
  apply MonoidHom.mem_ker.mpr
  have himage := Subgroup.mem_map_of_mem homomorphism helement
  rw [htrivial] at himage
  exact Subgroup.mem_bot.mp himage

end CFSG.RankThreeCoreUniqueness.Helpers
