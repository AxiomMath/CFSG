module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding

public section

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {Actor : Type*} [Group Actor] [Fintype Actor]
variable {Source : Type*} [AddCommGroup Source] [DistribMulAction Actor Source]

@[expose] def coprimeActionTrace (element : Source) : Source :=
  ∑ actingElement : Actor, actingElement • element

theorem coprimeActionTrace_fixed (element : Source) (actingElement : Actor) :
    actingElement • coprimeActionTrace (Actor := Actor) element =
      coprimeActionTrace (Actor := Actor) element := by
  unfold coprimeActionTrace
  rw [Finset.smul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft actingElement)
    (fun other => actingElement • other • element) (fun other => other • element)
    (fun other => (mul_smul actingElement other element).symm)

theorem coprimeActionTrace_map {Target : Type*} [AddCommGroup Target]
    [DistribMulAction Actor Target] (homomorphism : Source →+ Target)
    (hequivariant : ∀ actingElement : Actor, ∀ element : Source,
      homomorphism (actingElement • element) = actingElement • homomorphism element)
    (element : Source) :
    homomorphism (coprimeActionTrace (Actor := Actor) element) =
      coprimeActionTrace (Actor := Actor) (homomorphism element) := by
  simp only [coprimeActionTrace, map_sum, hequivariant]

theorem coprimeActionTrace_of_fixed (element : Source)
    (hfixed : ∀ actingElement : Actor, actingElement • element = element) :
    coprimeActionTrace (Actor := Actor) element = Fintype.card Actor • element := by
  simp only [coprimeActionTrace, hfixed, Finset.sum_const, Finset.card_univ]

theorem coprime_abelian_fixed_lift [Finite Source]
    {Target : Type*} [AddCommGroup Target] [Finite Target] [DistribMulAction Actor Target]
    (homomorphism : Source →+ Target) (hsurjective : Function.Surjective homomorphism)
    (hequivariant : ∀ actingElement : Actor, ∀ element : Source,
      homomorphism (actingElement • element) = actingElement • homomorphism element)
    (hsourceCoprime : (Nat.card Source).Coprime (Fintype.card Actor))
    (element : Target) (hfixed : ∀ actingElement : Actor, actingElement • element = element) :
    ∃ preimage : Source, homomorphism preimage = element ∧
      ∀ actingElement : Actor, actingElement • preimage = preimage := by
  have hcardDvd : Nat.card Target ∣ Nat.card Source := by
    have hdivisibility := AddSubgroup.card_range_dvd homomorphism
    rwa [homomorphism.range_eq_top_of_surjective hsurjective, AddSubgroup.card_top] at hdivisibility
  have htargetCoprime := hsourceCoprime.of_dvd_left hcardDvd
  obtain ⟨sourceElement, hsource⟩ := hsurjective element
  let trace := coprimeActionTrace (Actor := Actor) sourceElement
  let preimage := (nsmulCoprime hsourceCoprime).symm trace
  have hscaled : Fintype.card Actor • preimage = trace := by
    exact (nsmulCoprime_apply hsourceCoprime preimage).symm.trans
      ((nsmulCoprime hsourceCoprime).apply_symm_apply trace)
  refine ⟨preimage, ?_, ?_⟩
  · apply (nsmulCoprime htargetCoprime).injective
    rw [nsmulCoprime_apply, nsmulCoprime_apply, ← map_nsmul, hscaled]
    dsimp only [trace]
    rw [coprimeActionTrace_map homomorphism hequivariant, hsource,
      coprimeActionTrace_of_fixed element hfixed]
  · intro actingElement
    apply (nsmulCoprime hsourceCoprime).injective
    rw [nsmulCoprime_apply, nsmulCoprime_apply]
    have hcommute : Fintype.card Actor • (actingElement • preimage) =
        actingElement • (Fintype.card Actor • preimage) := by
      induction Fintype.card Actor with
      | zero => simp
      | succ count inductionHypothesis =>
        simp only [succ_nsmul, smul_add, inductionHypothesis]
    rw [hcommute, hscaled]
    exact coprimeActionTrace_fixed sourceElement actingElement

end CFSG.RankThreeCoreUniqueness.Helpers

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem finite_field_line_sum_identity
    {FieldType : Type*} [Field FieldType] [Fintype FieldType]
    {Value : Type*} [AddCommGroup Value] (function : FieldType → FieldType → Value) :
    (∑ slope : FieldType, ∑ coordinate : FieldType, function coordinate (slope * coordinate)) +
        (∑ coordinate : FieldType, function 0 coordinate) =
      (∑ first : FieldType, ∑ second : FieldType, function first second) +
        Fintype.card FieldType • function 0 0 := by
  classical
  have hnonzero : ∀ coordinate : FieldType, coordinate ≠ 0 →
      (∑ slope : FieldType, function coordinate (slope * coordinate)) =
        ∑ second : FieldType, function coordinate second := by
    intro coordinate hcoordinate
    exact Fintype.sum_equiv (Equiv.mulRight₀ coordinate hcoordinate)
      (fun slope => function coordinate (slope * coordinate))
      (fun second => function coordinate second) (fun slope => rfl)
  rw [Finset.sum_comm]
  have hdiagonal := Finset.sum_erase_add (Finset.univ : Finset FieldType)
    (fun coordinate => ∑ slope : FieldType, function coordinate (slope * coordinate))
    (Finset.mem_univ (0 : FieldType))
  have htotal := Finset.sum_erase_add (Finset.univ : Finset FieldType)
    (fun first => ∑ second : FieldType, function first second)
    (Finset.mem_univ (0 : FieldType))
  rw [← hdiagonal, ← htotal]
  have hsum : (∑ coordinate ∈ (Finset.univ : Finset FieldType).erase 0,
      ∑ slope : FieldType, function coordinate (slope * coordinate)) =
      ∑ first ∈ (Finset.univ : Finset FieldType).erase 0,
        ∑ second : FieldType, function first second := by
    apply Finset.sum_congr rfl
    intro coordinate hcoordinate
    exact hnonzero coordinate (Finset.mem_erase.mp hcoordinate).1
  rw [hsum]
  simp only [mul_zero, Finset.sum_const, Finset.card_univ]
  abel

theorem finite_field_coprime_fixed_lines_generate
    {FieldType : Type*} [Field FieldType] [Fintype FieldType]
    {Value : Type*} [AddCommGroup Value] [Finite Value]
    [DistribMulAction (Multiplicative (FieldType × FieldType)) Value]
    (overgroup : AddSubgroup Value)
    (hcoprime : (Fintype.card FieldType).Coprime (Nat.card Value))
    (hlines : ∀ slope : FieldType, ∀ element : Value,
      (∀ coordinate : FieldType,
        Multiplicative.ofAdd (coordinate, slope * coordinate) • element = element) →
      element ∈ overgroup)
    (hvertical : ∀ element : Value,
      (∀ coordinate : FieldType,
        Multiplicative.ofAdd ((0 : FieldType), coordinate) • element = element) →
      element ∈ overgroup) : overgroup = ⊤ := by
  classical
  apply top_unique
  intro element _
  let actionFunction := fun first second : FieldType =>
    Multiplicative.ofAdd (first, second) • element
  have hlineTrace : ∀ slope : FieldType,
      (∑ coordinate : FieldType, actionFunction coordinate (slope * coordinate)) ∈ overgroup := by
    intro slope
    apply hlines slope
    intro coordinate
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.addLeft coordinate)
    intro other
    dsimp only [actionFunction]
    rw [← mul_smul]
    congr 1
    change (coordinate + other, slope * coordinate + slope * other) =
      (coordinate + other, slope * (coordinate + other))
    simp only [mul_add]
  have hverticalTrace : (∑ coordinate : FieldType, actionFunction 0 coordinate) ∈ overgroup := by
    apply hvertical
    intro coordinate
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.addLeft coordinate)
    intro other
    dsimp only [actionFunction]
    rw [← mul_smul]
    congr 1
    change (0 + 0, coordinate + other) = (0, coordinate + other)
    simp
  have htotalTrace : (∑ first : FieldType, ∑ second : FieldType,
      actionFunction first second) ∈ overgroup := by
    apply hvertical
    intro coordinate
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.addLeft coordinate)
    intro second
    dsimp only [actionFunction]
    rw [← mul_smul]
    congr 1
    change (0 + first, coordinate + second) = (first, coordinate + second)
    simp
  have hsum : ((∑ slope : FieldType, ∑ coordinate : FieldType,
      actionFunction coordinate (slope * coordinate)) +
      (∑ coordinate : FieldType, actionFunction 0 coordinate)) ∈ overgroup :=
    overgroup.add_mem (overgroup.sum_mem (fun slope _ => hlineTrace slope)) hverticalTrace
  rw [finite_field_line_sum_identity actionFunction] at hsum
  have hscaled := overgroup.sub_mem hsum htotalTrace
  have hmultiple : Fintype.card FieldType • element ∈ overgroup := by
    simpa only [actionFunction, show Multiplicative.ofAdd ((0 : FieldType), (0 : FieldType)) =
      (1 : Multiplicative (FieldType × FieldType)) from rfl, one_smul, add_sub_cancel_left] using hscaled
  have horderCoprime := hcoprime.of_dvd_right (addOrderOf_dvd_natCard element)
  obtain ⟨multiple, hmultipleEq⟩ := exists_nsmul_eq_self_of_coprime horderCoprime
  rw [← hmultipleEq]
  exact overgroup.nsmul_mem hmultiple multiple

@[expose] def fixedAddSubgroupOfHom
    {Actor OtherActor Value : Type*} [Monoid Actor] [Monoid OtherActor] [AddGroup Value]
    [DistribMulAction Actor Value] (homomorphism : OtherActor →* Actor) : AddSubgroup Value where
  carrier := {element | ∀ actingElement : OtherActor, homomorphism actingElement • element = element}
  zero_mem' := fun _ => smul_zero _
  add_mem' := by
    intro first second hfirst hsecond actingElement
    rw [smul_add, hfirst actingElement, hsecond actingElement]
  neg_mem' := by
    intro element helement actingElement
    rw [smul_neg, helement actingElement]

@[expose, instance_reducible]
def fixedAddSubgroupOfHomAction
    {Actor OtherActor Value : Type*} [CommMonoid Actor] [Monoid OtherActor] [AddGroup Value]
    [DistribMulAction Actor Value] (homomorphism : OtherActor →* Actor) :
    DistribMulAction Actor (fixedAddSubgroupOfHom (Value := Value) homomorphism) where
  smul actingElement element := ⟨actingElement • element, by
    intro other
    rw [smul_comm, element.property other]⟩
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
    exact smul_add _ _ _

@[expose] def scalarLineHom {FieldType : Type*} [Field FieldType] (vector : FieldType × FieldType × FieldType) :
    Multiplicative FieldType →* Multiplicative (FieldType × FieldType × FieldType) where
  toFun coordinate := Multiplicative.ofAdd (Multiplicative.toAdd coordinate • vector)
  map_one' := by
    change (0 : FieldType) • vector = 0
    exact zero_smul _ _
  map_mul' := by
    intro first second
    change (Multiplicative.toAdd first + Multiplicative.toAdd second) • vector =
      Multiplicative.toAdd first • vector + Multiplicative.toAdd second • vector
    exact add_smul _ _ _

@[expose] def coordinatePlaneHom {FieldType : Type*} [CommSemiring FieldType]
    (first second : FieldType × FieldType × FieldType) :
    Multiplicative (FieldType × FieldType) →* Multiplicative (FieldType × FieldType × FieldType) where
  toFun coordinate := Multiplicative.ofAdd
    ((Multiplicative.toAdd coordinate).1 • first + (Multiplicative.toAdd coordinate).2 • second)
  map_one' := by
    change (0 : FieldType) • first + (0 : FieldType) • second = 0
    simp
  map_mul' := by
    intro source target
    change ((Multiplicative.toAdd source).1 + (Multiplicative.toAdd target).1) • first +
      ((Multiplicative.toAdd source).2 + (Multiplicative.toAdd target).2) • second =
      ((Multiplicative.toAdd source).1 • first + (Multiplicative.toAdd source).2 • second) +
      ((Multiplicative.toAdd target).1 • first + (Multiplicative.toAdd target).2 • second)
    simp only [add_smul]
    abel

theorem coprime_fixed_line_le_of_complementary_plane
    {FieldType : Type*} [Field FieldType] [Fintype FieldType]
    {Value : Type*} [AddCommGroup Value] [Finite Value]
    [DistribMulAction (Multiplicative (FieldType × FieldType × FieldType)) Value]
    (overgroup : AddSubgroup Value)
    (hcoprime : (Fintype.card FieldType).Coprime (Nat.card Value))
    (vector first second : FieldType × FieldType × FieldType)
    (hindependent : ∀ vectorCoefficient firstCoefficient secondCoefficient : FieldType,
      vectorCoefficient • vector + firstCoefficient • first + secondCoefficient • second = 0 →
      vectorCoefficient = 0 ∧ firstCoefficient = 0 ∧ secondCoefficient = 0)
    (hplanes : ∀ firstVector secondVector : FieldType × FieldType × FieldType,
      LinearIndependent FieldType ![firstVector, secondVector] →
      ∀ element : Value,
        (∀ coordinate : FieldType, scalarLineHom firstVector (Multiplicative.ofAdd coordinate) •
          element = element) →
        (∀ coordinate : FieldType, scalarLineHom secondVector (Multiplicative.ofAdd coordinate) •
          element = element) → element ∈ overgroup) :
    fixedAddSubgroupOfHom (Value := Value) (scalarLineHom vector) ≤ overgroup := by
  let fixedGroup := fixedAddSubgroupOfHom (Value := Value) (scalarLineHom vector)
  let : DistribMulAction (Multiplicative (FieldType × FieldType × FieldType)) fixedGroup :=
    fixedAddSubgroupOfHomAction (scalarLineHom vector)
  let : DistribMulAction (Multiplicative (FieldType × FieldType)) fixedGroup :=
    DistribMulAction.compHom fixedGroup (coordinatePlaneHom first second)
  have hfixedCoprime : (Fintype.card FieldType).Coprime (Nat.card fixedGroup) :=
    hcoprime.of_dvd_right (AddSubgroup.card_dvd_of_injective fixedGroup.subtype
      fixedGroup.subtype_injective)
  have hlineIndependent : ∀ slope : FieldType,
      LinearIndependent FieldType ![vector, first + slope • second] := by
    intro slope
    apply LinearIndependent.pair_iff.mpr
    intro vectorCoefficient lineCoefficient hequal
    have hzero : vectorCoefficient • vector + lineCoefficient • first +
        (lineCoefficient * slope) • second = 0 := by
      simpa only [smul_add, smul_smul, one_smul, add_assoc] using hequal
    have hcoefficients := hindependent vectorCoefficient lineCoefficient (lineCoefficient * slope) hzero
    exact ⟨hcoefficients.1, hcoefficients.2.1⟩
  have hsecondIndependent : LinearIndependent FieldType ![vector, second] := by
    apply LinearIndependent.pair_iff.mpr
    intro vectorCoefficient secondCoefficient hequal
    have hzero : vectorCoefficient • vector + (0 : FieldType) • first +
        secondCoefficient • second = 0 := by
      simpa only [zero_smul, add_zero] using hequal
    have hcoefficients := hindependent vectorCoefficient 0 secondCoefficient hzero
    exact ⟨hcoefficients.1, hcoefficients.2.2⟩
  have hfull : overgroup.comap fixedGroup.subtype = ⊤ := by
    apply finite_field_coprime_fixed_lines_generate _ hfixedCoprime
    · intro slope element hfixed
      apply hplanes vector (first + slope • second) (hlineIndependent slope) element
      · intro coordinate
        exact element.property (Multiplicative.ofAdd coordinate)
      · intro coordinate
        have hambient := congrArg (fun fixedElement : fixedGroup => (fixedElement : Value))
          (hfixed coordinate)
        change coordinatePlaneHom first second
          (Multiplicative.ofAdd (coordinate, slope * coordinate)) • (element : Value) = element
          at hambient
        have hequal : coordinatePlaneHom first second
            (Multiplicative.ofAdd (coordinate, slope * coordinate)) =
            scalarLineHom (first + slope • second) (Multiplicative.ofAdd coordinate) := by
          change coordinate • first + (slope * coordinate) • second =
            coordinate • (first + slope • second)
          rw [smul_add, smul_smul, mul_comm slope coordinate]
        rwa [hequal] at hambient
    · intro element hfixed
      apply hplanes vector second hsecondIndependent element
      · intro coordinate
        exact element.property (Multiplicative.ofAdd coordinate)
      · intro coordinate
        have hambient := congrArg (fun fixedElement : fixedGroup => (fixedElement : Value))
          (hfixed coordinate)
        change coordinatePlaneHom first second
          (Multiplicative.ofAdd ((0 : FieldType), coordinate)) • (element : Value) = element
          at hambient
        have hequal : coordinatePlaneHom first second
            (Multiplicative.ofAdd ((0 : FieldType), coordinate)) =
            scalarLineHom second (Multiplicative.ofAdd coordinate) := by
          change (0 : FieldType) • first + coordinate • second = coordinate • second
          simp
        rwa [hequal] at hambient
  intro element helement
  exact show (⟨element, helement⟩ : fixedGroup) ∈ overgroup.comap fixedGroup.subtype from
    hfull ▸ AddSubgroup.mem_top _

theorem finite_field_coprime_fixed_planes_generate
    {FieldType : Type*} [Field FieldType] [Fintype FieldType]
    {Value : Type*} [AddCommGroup Value] [Finite Value]
    [DistribMulAction (Multiplicative (FieldType × FieldType × FieldType)) Value]
    (overgroup : AddSubgroup Value)
    (hcoprime : (Fintype.card FieldType).Coprime (Nat.card Value))
    (hplanes : ∀ firstVector secondVector : FieldType × FieldType × FieldType,
      LinearIndependent FieldType ![firstVector, secondVector] →
      ∀ element : Value,
        (∀ coordinate : FieldType, scalarLineHom firstVector (Multiplicative.ofAdd coordinate) •
          element = element) →
        (∀ coordinate : FieldType, scalarLineHom secondVector (Multiplicative.ofAdd coordinate) •
          element = element) → element ∈ overgroup) : overgroup = ⊤ := by
  let firstBasis : FieldType × FieldType × FieldType := (1, 0, 0)
  let secondBasis : FieldType × FieldType × FieldType := (0, 1, 0)
  let thirdBasis : FieldType × FieldType × FieldType := (0, 0, 1)
  let : DistribMulAction (Multiplicative (FieldType × FieldType)) Value :=
    DistribMulAction.compHom Value (coordinatePlaneHom firstBasis secondBasis)
  apply finite_field_coprime_fixed_lines_generate overgroup hcoprime
  · intro slope element hfixed
    let vector := firstBasis + slope • secondBasis
    have hindependent : ∀ vectorCoefficient firstCoefficient secondCoefficient : FieldType,
        vectorCoefficient • vector + firstCoefficient • secondBasis +
          secondCoefficient • thirdBasis = 0 →
        vectorCoefficient = 0 ∧ firstCoefficient = 0 ∧ secondCoefficient = 0 := by
      intro vectorCoefficient firstCoefficient secondCoefficient hequal
      have hfirst := congrArg Prod.fst hequal
      have hsecond := congrArg (fun coordinate : FieldType × FieldType × FieldType =>
        coordinate.2.1) hequal
      have hthird := congrArg (fun coordinate : FieldType × FieldType × FieldType =>
        coordinate.2.2) hequal
      simp [vector, firstBasis, secondBasis, thirdBasis] at hfirst hsecond hthird
      exact ⟨hfirst, by simpa [hfirst] using hsecond, hthird⟩
    apply coprime_fixed_line_le_of_complementary_plane overgroup hcoprime vector secondBasis
      thirdBasis hindependent hplanes
    intro actingElement
    have hknown := hfixed (Multiplicative.toAdd actingElement)
    change coordinatePlaneHom firstBasis secondBasis
      (Multiplicative.ofAdd (Multiplicative.toAdd actingElement,
        slope * Multiplicative.toAdd actingElement)) • element = element at hknown
    have hequal : coordinatePlaneHom firstBasis secondBasis
        (Multiplicative.ofAdd (Multiplicative.toAdd actingElement,
          slope * Multiplicative.toAdd actingElement)) = scalarLineHom vector actingElement := by
      change Multiplicative.toAdd actingElement • firstBasis +
        (slope * Multiplicative.toAdd actingElement) • secondBasis =
        Multiplicative.toAdd actingElement • (firstBasis + slope • secondBasis)
      rw [smul_add, smul_smul, mul_comm slope (Multiplicative.toAdd actingElement)]
    rwa [hequal] at hknown
  · intro element hfixed
    have hindependent : ∀ vectorCoefficient firstCoefficient secondCoefficient : FieldType,
        vectorCoefficient • secondBasis + firstCoefficient • firstBasis +
          secondCoefficient • thirdBasis = 0 →
        vectorCoefficient = 0 ∧ firstCoefficient = 0 ∧ secondCoefficient = 0 := by
      intro vectorCoefficient firstCoefficient secondCoefficient hequal
      have hfirst := congrArg Prod.fst hequal
      have hsecond := congrArg (fun coordinate : FieldType × FieldType × FieldType =>
        coordinate.2.1) hequal
      have hthird := congrArg (fun coordinate : FieldType × FieldType × FieldType =>
        coordinate.2.2) hequal
      simp [firstBasis, secondBasis, thirdBasis] at hfirst hsecond hthird
      exact ⟨hsecond, hfirst, hthird⟩
    apply coprime_fixed_line_le_of_complementary_plane overgroup hcoprime secondBasis firstBasis
      thirdBasis hindependent hplanes
    intro actingElement
    have hknown := hfixed (Multiplicative.toAdd actingElement)
    change coordinatePlaneHom firstBasis secondBasis
      (Multiplicative.ofAdd ((0 : FieldType), Multiplicative.toAdd actingElement)) • element = element
      at hknown
    have hequal : coordinatePlaneHom firstBasis secondBasis
        (Multiplicative.ofAdd ((0 : FieldType), Multiplicative.toAdd actingElement)) =
        scalarLineHom secondBasis actingElement := by
      change (0 : FieldType) • firstBasis + Multiplicative.toAdd actingElement • secondBasis =
        Multiplicative.toAdd actingElement • secondBasis
      simp
    rwa [hequal] at hknown

end CFSG.RankThreeCoreUniqueness.Helpers

namespace CFSG.RankThreeCoreUniqueness.Helpers

open CFSG.Open

@[expose, instance_reducible]
def additiveActionOfMulAutHom
    {ActingGroup : Type*} [Monoid ActingGroup] {ValueGroup : Type*} [Group ValueGroup]
    (action : ActingGroup →* MulAut ValueGroup) :
    DistribMulAction ActingGroup (Additive ValueGroup) where
  smul actingElement element := Additive.ofMul (action actingElement (Additive.toMul element))
  one_smul := by
    intro element
    change action 1 (Additive.toMul element) = Additive.toMul element
    rw [map_one]
    rfl
  mul_smul := by
    intro first second element
    change action (first * second) (Additive.toMul element) =
      action first (action second (Additive.toMul element))
    rw [map_mul]
    rfl
  smul_zero := by
    intro actingElement
    change action actingElement 1 = 1
    exact map_one _
  smul_add := by
    intro actingElement first second
    change action actingElement (Additive.toMul first * Additive.toMul second) =
      action actingElement (Additive.toMul first) * action actingElement (Additive.toMul second)
    exact map_mul _ _ _

theorem embedded_coordinate_plane_rank_at_least_two
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding)
    (first second : ZMod prime × ZMod prime × ZMod prime)
    (hindependent : LinearIndependent (ZMod prime) ![first, second]) :
    2 ≤ pRank prime (embedding.comp (coordinatePlaneHom first second)).range := by
  let : Fact prime.Prime := ⟨hprime⟩
  let planeEmbedding := embedding.comp (coordinatePlaneHom first second)
  have hplaneInjective : Function.Injective planeEmbedding := by
    intro source target hequal
    have hcoordinates := hinjective hequal
    change (Multiplicative.toAdd source).1 • first + (Multiplicative.toAdd source).2 • second =
      (Multiplicative.toAdd target).1 • first + (Multiplicative.toAdd target).2 • second at hcoordinates
    have hcoefficients := hindependent.eq_of_pair hcoordinates
    exact Prod.ext hcoefficients.1 hcoefficients.2
  have helementary : IsElemAbelian prime planeEmbedding.range := by
    constructor
    · infer_instance
    · rintro element ⟨source, rfl⟩
      rw [← map_pow]
      have hexponent : source ^ prime = 1 := by
        change prime • Multiplicative.toAdd source = 0
        apply Prod.ext <;> simp [nsmul_eq_mul]
      rw [hexponent, map_one]
  have hcard : Nat.card planeEmbedding.range = prime ^ 2 := by
    have hcardRange := Nat.card_range_of_injective hplaneInjective
    change Nat.card planeEmbedding.range = _ at hcardRange
    rw [hcardRange]
    change Nat.card (ZMod prime × ZMod prime) = prime ^ 2
    rw [Nat.card_prod, Nat.card_zmod, pow_two]
  unfold pRank
  exact le_csSup (pRank_set_bddAbove prime hprime.one_lt planeEmbedding.range)
    ⟨planeEmbedding.range, le_rfl, helementary, hcard⟩

theorem embedded_rank_three_abelian_signalizer_le_of_plane_centralizers
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (signalizer overgroup : Subgroup G)
    (hcommutative : IsMulCommutative signalizer)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer))
    (hcentralizers : ∀ first second : ZMod prime × ZMod prime × ZMod prime,
      LinearIndependent (ZMod prime) ![first, second] →
      signalizer ⊓ Subgroup.centralizer
        ((embedding.comp (coordinatePlaneHom first second)).range : Set G) ≤ overgroup) :
    signalizer ≤ overgroup := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative signalizer := hcommutative
  let : CommGroup signalizer := { (inferInstance : Group signalizer) with
    mul_comm := hcommutative.is_comm.comm }
  let normalizerHom := embedding.codRestrict (Subgroup.normalizer (signalizer : Set G))
    (fun element => hinvariant ⟨element, rfl⟩)
  let action := signalizer.normalizerMonoidHom.comp normalizerHom
  let : DistribMulAction (Multiplicative (ZMod prime × ZMod prime × ZMod prime))
      (Additive signalizer) := additiveActionOfMulAutHom action
  let additiveOvergroup := Subgroup.toAddSubgroup (overgroup.subgroupOf signalizer)
  have hfixedImpliesCentralizes
      (element : Additive signalizer)
      (first second : ZMod prime × ZMod prime × ZMod prime)
      (hfirst : ∀ coordinate : ZMod prime,
        scalarLineHom first (Multiplicative.ofAdd coordinate) • element = element)
      (hsecond : ∀ coordinate : ZMod prime,
        scalarLineHom second (Multiplicative.ofAdd coordinate) • element = element) :
      ((Additive.toMul element : signalizer) : G) ∈ Subgroup.centralizer
        ((embedding.comp (coordinatePlaneHom first second)).range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro actingElement ⟨coordinate, rfl⟩
    have hcoordinateFixed : coordinatePlaneHom first second coordinate • element = element := by
      have hsplit : coordinatePlaneHom first second coordinate =
          scalarLineHom first (Multiplicative.ofAdd (Multiplicative.toAdd coordinate).1) *
            scalarLineHom second (Multiplicative.ofAdd (Multiplicative.toAdd coordinate).2) := rfl
      rw [hsplit, mul_smul, hsecond, hfirst]
    have hambient := congrArg (fun fixedElement : Additive signalizer =>
      ((Additive.toMul fixedElement : signalizer) : G)) hcoordinateFixed
    change ↑(signalizer.normalizerMonoidHom
      (normalizerHom (coordinatePlaneHom first second coordinate))
      (Additive.toMul element)) = ((Additive.toMul element : signalizer) : G) at hambient
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hambient
    change embedding (coordinatePlaneHom first second coordinate) *
      ((Additive.toMul element : signalizer) : G) *
        (embedding (coordinatePlaneHom first second coordinate))⁻¹ =
          ((Additive.toMul element : signalizer) : G) at hambient
    exact mul_inv_eq_iff_eq_mul.mp hambient
  have hfull : additiveOvergroup = ⊤ := by
    apply finite_field_coprime_fixed_planes_generate (FieldType := ZMod prime) additiveOvergroup
    · rw [← Nat.card_congr (Additive.ofMul : signalizer ≃ Additive signalizer)]
      simpa [Nat.card_eq_fintype_card] using hcoprime
    · intro first second hindependent element hfirst hsecond
      exact hcentralizers first second hindependent
        ⟨(Additive.toMul element).property,
          hfixedImpliesCentralizes element first second hfirst hsecond⟩
  intro element helement
  exact show (Additive.ofMul (⟨element, helement⟩ : signalizer)) ∈ additiveOvergroup from
    hfull ▸ AddSubgroup.mem_top _

theorem embedded_coordinate_rank_at_least_three
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding) : 3 ≤ pRank prime embedding.range := by
  have helementary : IsElemAbelian prime embedding.range := by
    constructor
    · infer_instance
    · rintro element ⟨source, rfl⟩
      rw [← map_pow]
      have hexponent : source ^ prime = 1 := by
        change prime • Multiplicative.toAdd source = 0
        apply Prod.ext
        · simp [nsmul_eq_mul]
        · apply Prod.ext <;> simp [nsmul_eq_mul]
      rw [hexponent, map_one]
  have hcard : Nat.card embedding.range = prime ^ 3 := by
    have hcardRange := Nat.card_range_of_injective hinjective
    change Nat.card embedding.range = _ at hcardRange
    rw [hcardRange]
    change Nat.card (ZMod prime × ZMod prime × ZMod prime) = prime ^ 3
    simp [Nat.card_prod, Nat.card_zmod, pow_succ, mul_assoc]
  unfold pRank
  exact le_csSup (pRank_set_bddAbove prime hprime.one_lt embedding.range)
    ⟨embedding.range, le_rfl, helementary, hcard⟩

theorem embedded_rank_three_abelian_signalizer_le_aschCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (embedding : Multiplicative (ZMod prime × ZMod prime × ZMod prime) →* G)
    (hinjective : Function.Injective embedding) (ambient signalizer : Subgroup G)
    (hinclusion : embedding.range ≤ ambient)
    (hcommutative : IsMulCommutative signalizer)
    (hinvariant : embedding.range ≤ Subgroup.normalizer (signalizer : Set G))
    (hcoprime : prime.Coprime (Nat.card signalizer)) :
    signalizer ≤ rankThreeAschCore 2 prime ambient := by
  apply embedded_rank_three_abelian_signalizer_le_of_plane_centralizers prime hprime
    embedding signalizer _ hcommutative hinvariant hcoprime
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
