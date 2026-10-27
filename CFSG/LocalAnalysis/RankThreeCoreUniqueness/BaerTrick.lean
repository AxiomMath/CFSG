module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

attribute [local instance] commutatorElement

theorem class_two_commutator_central
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value) (first second : Value) :
    ⁅first, second⁆ ∈ Subgroup.center Value := by
  exact hclassTwo (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem class_two_commutator_mul_left
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value) (first second third : Value) :
    ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (Subgroup.mem_center_iff.mp (class_two_commutator_central hclassTwo second third) first),
    mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp
    (class_two_commutator_central hclassTwo first third) ⁅second, third⁆)

theorem class_two_commutator_mul_right
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value) (first second third : Value) :
    ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hcentral := Subgroup.mem_center_iff.mp
    (class_two_commutator_central hclassTwo first third) second
  calc
    ⁅first, second⁆ * second * ⁅first, third⁆ * second⁻¹ =
        ⁅first, second⁆ * (second * ⁅first, third⁆) * second⁻¹ := by
          simp only [mul_assoc]
    _ = ⁅first, second⁆ * (⁅first, third⁆ * second) * second⁻¹ := by rw [hcentral]
    _ = ⁅first, second⁆ * ⁅first, third⁆ := by group

@[expose] def baerCorrection {Value : Type*} [Group Value] (halfExponent : ℕ)
    (first second : Value) : Value := ⁅second, first⁆ ^ halfExponent

@[expose] def baerOperation {Value : Type*} [Group Value] (halfExponent : ℕ)
    (first second : Value) : Value := first * second * baerCorrection halfExponent first second

theorem baerCorrection_central
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (first second : Value) :
    baerCorrection halfExponent first second ∈ Subgroup.center Value :=
  (Subgroup.center Value).pow_mem (class_two_commutator_central hclassTwo second first) _

theorem baerCorrection_mul_left
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (first second third : Value) :
    baerCorrection halfExponent (first * second) third =
      baerCorrection halfExponent first third * baerCorrection halfExponent second third := by
  unfold baerCorrection
  rw [class_two_commutator_mul_right hclassTwo]
  exact (commute_iff_eq _ _).mpr
    (Subgroup.mem_center_iff.mp (class_two_commutator_central hclassTwo third second)
      ⁅third, first⁆) |>.mul_pow _

theorem baerCorrection_mul_right
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (first second third : Value) :
    baerCorrection halfExponent first (second * third) =
      baerCorrection halfExponent first second * baerCorrection halfExponent first third := by
  unfold baerCorrection
  rw [class_two_commutator_mul_left hclassTwo]
  exact (commute_iff_eq _ _).mpr
    (Subgroup.mem_center_iff.mp (class_two_commutator_central hclassTwo third first)
      ⁅second, first⁆) |>.mul_pow _

theorem baerCorrection_of_central_left
    {Value : Type*} [Group Value] (halfExponent : ℕ) (first second : Value)
    (hcentral : first ∈ Subgroup.center Value) : baerCorrection halfExponent first second = 1 := by
  unfold baerCorrection
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcentral second),
    one_pow]

theorem baerCorrection_of_central_right
    {Value : Type*} [Group Value] (halfExponent : ℕ) (first second : Value)
    (hcentral : second ∈ Subgroup.center Value) : baerCorrection halfExponent first second = 1 := by
  unfold baerCorrection
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcentral first).symm,
    one_pow]

theorem baerOperation_assoc
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (first second third : Value) :
    baerOperation halfExponent (baerOperation halfExponent first second) third =
      baerOperation halfExponent first (baerOperation halfExponent second third) := by
  have hfirstCorrection := baerCorrection_central hclassTwo halfExponent first second
  have hsecondCorrection := baerCorrection_central hclassTwo halfExponent second third
  unfold baerOperation
  rw [baerCorrection_mul_left hclassTwo, baerCorrection_mul_left hclassTwo,
    baerCorrection_mul_right hclassTwo, baerCorrection_mul_right hclassTwo,
    baerCorrection_of_central_left _ _ _ hfirstCorrection,
    baerCorrection_of_central_right _ _ _ hsecondCorrection, mul_one, mul_one]
  have hcommuteThird := Subgroup.mem_center_iff.mp hfirstCorrection third
  simp only [mul_assoc]
  apply congrArg (fun value : Value => first * (second * value))
  calc
    baerCorrection halfExponent first second *
        (third * (baerCorrection halfExponent first third * baerCorrection halfExponent second third)) =
      third * (baerCorrection halfExponent first second *
        (baerCorrection halfExponent first third * baerCorrection halfExponent second third)) := by
          rw [← mul_assoc (baerCorrection halfExponent first second) third,
            ← hcommuteThird, mul_assoc]
    _ = third * (baerCorrection halfExponent second third *
        (baerCorrection halfExponent first second * baerCorrection halfExponent first third)) := by
          apply congrArg (fun value : Value => third * value)
          rw [← mul_assoc]
          exact Subgroup.mem_center_iff.mp hsecondCorrection
            (baerCorrection halfExponent first second * baerCorrection halfExponent first third)

theorem baerOperation_comm
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (hhalf : ∀ element : Value, element ^ (2 * halfExponent) = element)
    (first second : Value) :
    baerOperation halfExponent first second = baerOperation halfExponent second first := by
  have hswap : first * second = second * first * ⁅first, second⁆ := by
    have hcentral := Subgroup.mem_center_iff.mp
      (class_two_commutator_central hclassTwo first second) (second * first)
    rw [hcentral]
    rw [commutatorElement_def]
    group
  have hinverse : baerCorrection halfExponent first second =
      (baerCorrection halfExponent second first)⁻¹ := by
    unfold baerCorrection
    rw [← commutatorElement_inv, inv_pow]
  have hcorrection : ⁅first, second⁆ =
      baerCorrection halfExponent second first * baerCorrection halfExponent second first := by
    unfold baerCorrection
    rw [← pow_add]
    have hexponents : halfExponent + halfExponent = 2 * halfExponent := by omega
    rw [hexponents, hhalf]
  unfold baerOperation
  rw [hswap, hinverse, hcorrection]
  group

@[expose] def BaerValue (Value : Type*) := Value

@[expose] def baerValueEquiv (Value : Type*) : BaerValue Value ≃ Value := Equiv.refl _

@[expose, instance_reducible]
def baerAddCommGroup
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (hhalf : ∀ element : Value, element ^ (2 * halfExponent) = element) :
    AddCommGroup (BaerValue Value) := by
  let : Add (BaerValue Value) := ⟨fun first second =>
    (baerValueEquiv Value).symm (baerOperation halfExponent
      (baerValueEquiv Value first) (baerValueEquiv Value second))⟩
  let : Zero (BaerValue Value) := ⟨(1 : Value)⟩
  let : Neg (BaerValue Value) := ⟨fun element =>
    (baerValueEquiv Value).symm (baerValueEquiv Value element)⁻¹⟩
  let additiveGroup : AddGroup (BaerValue Value) := AddGroup.ofLeftAxioms
    (fun first second third => baerOperation_assoc hclassTwo halfExponent
      (baerValueEquiv Value first) (baerValueEquiv Value second) (baerValueEquiv Value third))
    (fun element => by
      change baerOperation halfExponent 1 (baerValueEquiv Value element) = baerValueEquiv Value element
      simp [baerOperation, baerCorrection])
    (fun element => by
      change baerOperation halfExponent (baerValueEquiv Value element)⁻¹
        (baerValueEquiv Value element) = 1
      simp [baerOperation, baerCorrection, commutatorElement_def])
  exact { additiveGroup with
    add_comm := fun first second =>
      baerOperation_comm hclassTwo halfExponent hhalf (baerValueEquiv Value first)
        (baerValueEquiv Value second) }

theorem baer_nsmul_eq_pow
    {Value : Type*} [Group Value]
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (hhalf : ∀ element : Value, element ^ (2 * halfExponent) = element)
    (exponent : ℕ) (element : BaerValue Value) :
    letI := baerAddCommGroup hclassTwo halfExponent hhalf
    baerValueEquiv Value (exponent • element) = baerValueEquiv Value element ^ exponent := by
  let : AddCommGroup (BaerValue Value) := baerAddCommGroup hclassTwo halfExponent hhalf
  induction exponent with
  | zero =>
    rw [zero_nsmul, pow_zero]
    rfl
  | succ exponent inductionHypothesis =>
    rw [succ_nsmul]
    change baerOperation halfExponent (baerValueEquiv Value (exponent • element))
      (baerValueEquiv Value element) = (baerValueEquiv Value element) ^ (exponent + 1)
    rw [inductionHypothesis]
    have hcommute : Commute (baerValueEquiv Value element)
        ((baerValueEquiv Value element) ^ exponent) :=
      Commute.self_pow _ _
    simp only [baerOperation, baerCorrection,
      commutatorElement_eq_one_iff_mul_comm.mpr hcommute.eq, one_pow, mul_one, pow_succ]

@[expose, instance_reducible]
def baerDistribMulAction
    {Actor Value : Type*} [Monoid Actor] [Group Value]
    (action : Actor →* MulAut Value)
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
    (halfExponent : ℕ) (hhalf : ∀ element : Value, element ^ (2 * halfExponent) = element) :
    letI := baerAddCommGroup hclassTwo halfExponent hhalf
    DistribMulAction Actor (BaerValue Value) := by
  let : AddCommGroup (BaerValue Value) := baerAddCommGroup hclassTwo halfExponent hhalf
  exact {
    smul := fun actingElement element =>
      (baerValueEquiv Value).symm (action actingElement (baerValueEquiv Value element))
    one_smul := by
      intro element
      change action 1 (baerValueEquiv Value element) = baerValueEquiv Value element
      rw [map_one]
      rfl
    mul_smul := by
      intro first second element
      change action (first * second) (baerValueEquiv Value element) =
        action first (action second (baerValueEquiv Value element))
      rw [map_mul]
      rfl
    smul_zero := by
      intro actingElement
      change action actingElement (1 : Value) = 1
      exact map_one _
    smul_add := by
      intro actingElement first second
      change action actingElement (baerOperation halfExponent
          (baerValueEquiv Value first) (baerValueEquiv Value second)) =
        baerOperation halfExponent (action actingElement (baerValueEquiv Value first))
          (action actingElement (baerValueEquiv Value second))
      simp only [baerOperation, baerCorrection, map_mul, map_pow, map_commutatorElement] }

theorem finite_odd_group_has_half_exponent
    {Value : Type*} [Group Value] [Finite Value]
    (hodd : Odd (Nat.card Value)) :
    ∃ halfExponent : ℕ, ∀ element : Value, element ^ (2 * halfExponent) = element := by
  obtain ⟨exponent, hcard⟩ := hodd
  refine ⟨exponent + 1, fun element => ?_⟩
  have hexponents : 2 * (exponent + 1) = Nat.card Value + 1 := by omega
  rw [hexponents, pow_succ, pow_card_eq_one', one_mul]

theorem class_two_odd_pGroup_normalized_actor_fixed_order_prime_lemma
    {Actor OtherActor Value : Type*} [Group Actor] [Group OtherActor] [Finite OtherActor]
    [Group Value] [Finite Value]
    [MulDistribMulAction Actor Value] [MulDistribMulAction OtherActor Value]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hactor : IsPGroup prime Actor) (hvalue : IsPGroup prime Value)
    (hclassTwo : commutator Value ≤ Subgroup.center Value)
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
  let : Fintype OtherActor := Fintype.ofFinite OtherActor
  obtain ⟨valueExponent, hvalueCard⟩ := IsPGroup.iff_card.mp hvalue
  have hoddCard : Odd (Nat.card Value) := by
    rw [hvalueCard]
    exact (hprime.odd_of_ne_two hodd).pow
  obtain ⟨halfExponent, hhalf⟩ := finite_odd_group_has_half_exponent hoddCard
  let : AddCommGroup (BaerValue Value) := baerAddCommGroup hclassTwo halfExponent hhalf
  let : Finite (BaerValue Value) := Finite.of_equiv Value (baerValueEquiv Value).symm
  let actorAction := MulDistribMulAction.toMulAut Actor Value
  let otherAction := MulDistribMulAction.toMulAut OtherActor Value
  let : DistribMulAction Actor (BaerValue Value) :=
    baerDistribMulAction actorAction hclassTwo halfExponent hhalf
  let : DistribMulAction OtherActor (BaerValue Value) :=
    baerDistribMulAction otherAction hclassTwo halfExponent hhalf
  have hbaerPGroup : IsPGroup prime (Multiplicative (BaerValue Value)) := by
    apply IsPGroup.of_card (n := valueExponent)
    rw [Nat.card_congr ((Multiplicative.toAdd : Multiplicative (BaerValue Value) ≃
      BaerValue Value).trans (baerValueEquiv Value)), hvalueCard]
  have hbaerCoprime : (Nat.card (BaerValue Value)).Coprime (Fintype.card OtherActor) := by
    rw [Nat.card_congr (baerValueEquiv Value)]
    simpa only [Nat.card_eq_fintype_card] using hcoprime
  have hbaerCompatibility : ∀ actingElement : Actor, ∀ otherElement : OtherActor,
      ∀ element : BaerValue Value,
      actingElement • otherElement • element =
        normalizingAction actingElement otherElement • actingElement • element := by
    intro actingElement otherElement element
    apply (baerValueEquiv Value).injective
    exact hcompatibility actingElement otherElement (baerValueEquiv Value element)
  have hbaerCentralizes : ∀ element : BaerValue Value, prime • element = 0 →
      (∀ actingElement : Actor, actingElement • element = element) →
      ∀ otherElement : OtherActor, otherElement • element = element := by
    intro element hkilled hfixed otherElement
    apply (baerValueEquiv Value).injective
    apply hcentralizes (baerValueEquiv Value element)
    · rw [← baer_nsmul_eq_pow hclassTwo halfExponent hhalf prime element, hkilled]
      rfl
    · intro actingElement
      exact congrArg (baerValueEquiv Value) (hfixed actingElement)
  have hresult := abelian_pGroup_normalized_actor_fixed_order_prime_lemma prime hprime
    hactor hbaerPGroup hbaerCoprime normalizingAction hbaerCompatibility hbaerCentralizes
  intro otherElement element
  exact congrArg (baerValueEquiv Value)
    (hresult otherElement ((baerValueEquiv Value).symm element))

end CFSG.RankThreeCoreUniqueness.Helpers
