module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact
public import CFSG.LocalAnalysis.LargeEvenClassification.NormObstruction

public section

namespace CFSG.LargeEvenClassification.Helpers

universe ringUniverse

theorem binary_nilpotent_multiple {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (element : CoefficientRing) :
    IsNilpotent (2 * element) := by
  refine ⟨exponent, ?_⟩
  rw [(Commute.ofNat_left 2 element).mul_pow, hcharacteristic, zero_mul]

theorem binary_one_add_double_isUnit {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (element : CoefficientRing) :
    IsUnit (1 + 2 * element) :=
  (binary_nilpotent_multiple hcharacteristic element).isUnit_one_add

theorem finite_binary_ring_characteristic {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] [Finite CoefficientRing]
    (hpgroup : IsPGroup 2 (Multiplicative CoefficientRing)) :
    ∃ exponent : ℕ, (2 : CoefficientRing) ^ exponent = 0 := by
  obtain ⟨exponent, hpow⟩ := hpgroup.exists_pow_pow_eq_one (Multiplicative.ofAdd (1 : CoefficientRing))
  have hsmul : (2 ^ exponent : ℕ) • (1 : CoefficientRing) = 0 := hpow
  refine ⟨exponent, ?_⟩
  simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] using hsmul

theorem principal_square_eq_iff_double_sub {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (first second : CoefficientRing) (hfirst : ∃ entry : CoefficientRing, first = 1 + 4 * entry)
    (hsecond : ∃ entry : CoefficientRing, second = 1 + 4 * entry) :
    first ^ 2 = second ^ 2 ↔ 2 * (first - second) = 0 := by
  obtain ⟨firstEntry, rfl⟩ := hfirst
  obtain ⟨secondEntry, rfl⟩ := hsecond
  let linearOperator : AddMonoid.End CoefficientRing :=
    AddMonoidHom.mulRight firstEntry + AddMonoidHom.mulLeft secondEntry
  have hcharacteristicOperator : (2 : AddMonoid.End CoefficientRing) ^ exponent = 0 := by
    rw [← Nat.cast_ofNat, ← Nat.cast_pow]
    apply AddMonoidHom.ext
    intro element
    change (2 ^ exponent : ℕ) • element = 0
    rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, hcharacteristic, zero_mul]
  have hinvertible := binary_one_add_double_isUnit hcharacteristicOperator linearOperator
  have hexpansion :
      (1 + 4 * firstEntry) ^ 2 - (1 + 4 * secondEntry) ^ 2 =
        (1 + 2 * linearOperator) (2 * ((1 + 4 * firstEntry) - (1 + 4 * secondEntry))) := by
    change (1 + 4 * firstEntry) ^ 2 - (1 + 4 * secondEntry) ^ 2 =
      2 * ((1 + 4 * firstEntry) - (1 + 4 * secondEntry)) +
        2 • (2 * ((1 + 4 * firstEntry) - (1 + 4 * secondEntry)) * firstEntry +
          secondEntry * (2 * ((1 + 4 * firstEntry) - (1 + 4 * secondEntry))))
    rw [nsmul_eq_mul]
    norm_num only [Nat.cast_ofNat]
    noncomm_ring
  rw [← sub_eq_zero, hexpansion]
  change (1 + 2 * linearOperator) •
      (2 * ((1 + 4 * firstEntry) - (1 + 4 * secondEntry))) = 0 ↔ _
  exact hinvertible.smul_eq_zero

theorem principal_involution_central {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (involution element : CoefficientRingˣ)
    (hinvolution : ∃ entry : CoefficientRing, (involution : CoefficientRing) = 1 + 4 * entry)
    (helement : ∃ entry : CoefficientRing, (element : CoefficientRing) = 1 + 4 * entry)
    (hsquare : involution ^ 2 = 1) : Commute involution element := by
  have hsquareRing : (involution : CoefficientRing) ^ 2 = 1 := congrArg Units.val hsquare
  have hdouble : 2 * ((involution : CoefficientRing) - 1) = 0 :=
    (principal_square_eq_iff_double_sub hcharacteristic involution 1 hinvolution
      ⟨0, by simp⟩).mp (by simpa using hsquareRing)
  obtain ⟨entry, hentry⟩ := helement
  have hleft : ((involution : CoefficientRing) - 1) * (4 * entry) = 0 := by
    calc
      _ = (2 * ((involution : CoefficientRing) - 1)) * (2 * entry) := by noncomm_ring
      _ = 0 := by rw [hdouble, zero_mul]
  have hright : (4 * entry) * ((involution : CoefficientRing) - 1) = 0 := by
    calc
      _ = (2 * entry) * (2 * ((involution : CoefficientRing) - 1)) := by noncomm_ring
      _ = 0 := by rw [hdouble, mul_zero]
  apply Units.ext
  change (involution : CoefficientRing) * element = (element : CoefficientRing) * involution
  rw [hentry]
  calc
    _ = 1 + ((involution : CoefficientRing) - 1) + 4 * entry +
        ((involution : CoefficientRing) - 1) * (4 * entry) := by noncomm_ring
    _ = 1 + ((involution : CoefficientRing) - 1) + 4 * entry +
        (4 * entry) * ((involution : CoefficientRing) - 1) := by rw [hleft, hright]
    _ = _ := by noncomm_ring

@[expose] def principalInvolutionSubgroup {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry) :
    Subgroup Principal := {
  carrier := {element | element ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro first second hfirst hsecond
    change first ^ 2 = 1 at hfirst
    change second ^ 2 = 1 at hsecond
    change (first * second) ^ 2 = 1
    have hcommute : Commute first second := by
      apply Subtype.ext
      exact principal_involution_central hcharacteristic first second
        (hprincipal first) (hprincipal second) (congrArg Subtype.val hfirst)
    rw [hcommute.mul_pow, hfirst, hsecond, one_mul]
  inv_mem' := by
    intro element helement
    change element ^ 2 = 1 at helement
    change element⁻¹ ^ 2 = 1
    rw [inv_pow, helement, inv_one] }

theorem principalInvolutionSubgroup_central {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry) :
    principalInvolutionSubgroup hcharacteristic Principal hprincipal ≤ Subgroup.center Principal := by
  intro element helement
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  exact principal_involution_central hcharacteristic element other
    (hprincipal element) (hprincipal other) (congrArg Subtype.val helement) |>.symm

theorem principalInvolutionSubgroup_elementary {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry) :
    CFSG.Open.IsElemAbelian 2
      (principalInvolutionSubgroup hcharacteristic Principal hprincipal) := by
  constructor
  · apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (principalInvolutionSubgroup_central hcharacteristic Principal hprincipal first.property) second |>.symm
  · intro element helement
    exact helement

theorem principal_square_fiber {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry)
    (first second : Principal) :
    first ^ 2 = second ^ 2 ↔
      second⁻¹ * first ∈ principalInvolutionSubgroup hcharacteristic Principal hprincipal := by
  constructor
  · intro hequal
    have hdouble := (principal_square_eq_iff_double_sub hcharacteristic first.val second.val
      (hprincipal first) (hprincipal second)).mp (congrArg (fun element : Principal =>
        (element.val : CoefficientRing)) hequal)
    have hdoubleProduct : 2 * (((second.val)⁻¹ : CoefficientRingˣ).val * first.val - 1) = 0 := by
      calc
        _ = ((second.val)⁻¹ : CoefficientRingˣ).val * (2 *
            ((first.val : CoefficientRing) - second.val)) := by
          calc
            _ = ((second.val)⁻¹ : CoefficientRingˣ).val * (2 *
                ((first.val : CoefficientRing) - second.val)) +
                2 * (((second.val)⁻¹ : CoefficientRingˣ).val * second.val - 1) := by noncomm_ring
            _ = _ := by rw [Units.inv_mul]; simp
        _ = 0 := by rw [hdouble, mul_zero]
    have hsquare := (principal_square_eq_iff_double_sub hcharacteristic
      ((second⁻¹ * first).val : CoefficientRing) 1 (hprincipal (second⁻¹ * first))
      ⟨0, by simp⟩).mpr hdoubleProduct
    apply Subtype.ext
    apply Units.ext
    simpa using hsquare
  · intro hinvolution
    have hcentral := principalInvolutionSubgroup_central hcharacteristic Principal hprincipal hinvolution
    have hcommute : Commute second (second⁻¹ * first) :=
      Subgroup.mem_center_iff.mp hcentral second
    calc
      first ^ 2 = (second * (second⁻¹ * first)) ^ 2 := by simp
      _ = second ^ 2 * (second⁻¹ * first) ^ 2 := hcommute.mul_pow 2
      _ = second ^ 2 := by rw [show (second⁻¹ * first) ^ 2 = 1 from hinvolution, mul_one]

theorem principal_frattini_card_le_involutions {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ) [Finite Principal] (hpgroup : IsPGroup 2 Principal)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry) :
    Nat.card (Principal ⧸ frattini Principal) ≤
      Nat.card (principalInvolutionSubgroup hcharacteristic Principal hprincipal) := by
  let Involutions := principalInvolutionSubgroup hcharacteristic Principal hprincipal
  let : Involutions.Normal := subgroup_normal_of_central Involutions
    (principalInvolutionSubgroup_central hcharacteristic Principal hprincipal)
  let squareProjection : Principal ⧸ Involutions → frattini Principal := Quotient.lift
    (fun element : Principal => ⟨element ^ 2, pGroup_pow_mem_frattini Nat.prime_two hpgroup element⟩)
    (by
      intro first second hrelated
      apply Subtype.ext
      exact ((principal_square_fiber hcharacteristic Principal hprincipal second first).mpr
        (QuotientGroup.leftRel_apply.mp hrelated)).symm)
  have hinjective : Function.Injective squareProjection := by
    intro firstCoset secondCoset heq
    obtain ⟨first, rfl⟩ := QuotientGroup.mk'_surjective Involutions firstCoset
    obtain ⟨second, rfl⟩ := QuotientGroup.mk'_surjective Involutions secondCoset
    have hsquare := congrArg (fun element : frattini Principal => (element : Principal)) heq
    change first ^ 2 = second ^ 2 at hsquare
    apply QuotientGroup.eq.mpr
    exact (principal_square_fiber hcharacteristic Principal hprincipal second first).mp hsquare.symm
  have hquotientCard := Nat.card_le_card_of_injective squareProjection hinjective
  have hfirstCard := Subgroup.card_eq_card_quotient_mul_card_subgroup Involutions
  have hsecondCard := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Principal)
  have hproduct := Nat.mul_le_mul_right (Nat.card Involutions) hquotientCard
  have hpositive : 0 < Nat.card (frattini Principal) := Nat.card_pos
  nlinarith

theorem principal_pGeneratorRank_le_involutions {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Principal : Subgroup CoefficientRingˣ) [Finite Principal] (hpgroup : IsPGroup 2 Principal)
    (hprincipal : ∀ element : Principal,
      ∃ entry : CoefficientRing, (element.val : CoefficientRing) = 1 + 4 * entry) :
    pGeneratorRank 2 Principal ≤
      Nat.log 2 (Nat.card (principalInvolutionSubgroup hcharacteristic Principal hprincipal)) := by
  exact Nat.log_mono_right (principal_frattini_card_le_involutions
    hcharacteristic Principal hpgroup hprincipal)

@[expose] def principalFourSubgroup (CoefficientRing : Type ringUniverse) [Ring CoefficientRing] :
    Subgroup CoefficientRingˣ := {
  carrier := {element | ∃ entry : CoefficientRing, (element : CoefficientRing) = 1 + 4 * entry}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro first second ⟨firstEntry, hfirst⟩ ⟨secondEntry, hsecond⟩
    refine ⟨firstEntry + secondEntry + 4 * firstEntry * secondEntry, ?_⟩
    change (first : CoefficientRing) * second = _
    rw [hfirst, hsecond]
    noncomm_ring
  inv_mem' := by
    rintro element ⟨entry, hentry⟩
    refine ⟨-((element⁻¹ : CoefficientRingˣ).val * entry), ?_⟩
    have hinverse : (element⁻¹ : CoefficientRingˣ).val * (1 + 4 * entry) = 1 := by
      rw [← hentry]
      exact Units.inv_mul element
    have hexpand : (element⁻¹ : CoefficientRingˣ).val * (1 + 4 * entry) =
        (element⁻¹ : CoefficientRingˣ).val + 4 * ((element⁻¹ : CoefficientRingˣ).val * entry) := by
      noncomm_ring
    rw [hexpand] at hinverse
    calc
      _ = 1 - 4 * ((element⁻¹ : CoefficientRingˣ).val * entry) := eq_sub_of_add_eq hinverse
      _ = _ := by noncomm_ring }

def fourAdditiveRange (CoefficientRing : Type ringUniverse) [Ring CoefficientRing] :
    AddSubgroup CoefficientRing := {
  carrier := {element | ∃ entry : CoefficientRing, element = 4 * entry}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro first second ⟨firstEntry, rfl⟩ ⟨secondEntry, rfl⟩
    exact ⟨firstEntry + secondEntry, (mul_add _ _ _).symm⟩
  neg_mem' := by
    rintro element ⟨entry, rfl⟩
    exact ⟨-entry, (mul_neg _ _).symm⟩ }

theorem principal_four_card_eq_additive_range {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0) :
    Nat.card (principalFourSubgroup CoefficientRing) = Nat.card (fourAdditiveRange CoefficientRing) := by
  let forward : principalFourSubgroup CoefficientRing → fourAdditiveRange CoefficientRing :=
    fun element => ⟨(element.val : CoefficientRing) - 1, by
      obtain ⟨entry, hentry⟩ := element.property
      exact ⟨entry, by rw [hentry]; simp⟩⟩
  have hinjective : Function.Injective forward := by
    intro first second heq
    apply Subtype.ext
    apply Units.ext
    exact sub_left_injective (congrArg Subtype.val heq)
  have hsurjective : Function.Surjective forward := by
    intro element
    obtain ⟨entry, hentry⟩ := element.property
    have hisUnit : IsUnit (1 + element.val) := by
      rw [hentry]
      have hfour : (4 : CoefficientRing) * entry = 2 * (2 * entry) := by noncomm_ring
      rw [hfour]
      exact binary_one_add_double_isUnit hcharacteristic (2 * entry)
    refine ⟨⟨hisUnit.unit, ?_⟩, ?_⟩
    · exact ⟨entry, by rw [hisUnit.unit_spec, hentry]⟩
    · apply Subtype.ext
      change (hisUnit.unit : CoefficientRing) - 1 = element.val
      rw [hisUnit.unit_spec]
      simp
  exact Nat.card_congr (Equiv.ofBijective forward ⟨hinjective, hsurjective⟩)

theorem principal_four_isPGroup {CoefficientRing : Type ringUniverse} [Ring CoefficientRing]
    [Finite CoefficientRing] (hpgroup : IsPGroup 2 (Multiplicative CoefficientRing)) :
    IsPGroup 2 (principalFourSubgroup CoefficientRing) := by
  obtain ⟨exponent, hcharacteristic⟩ := finite_binary_ring_characteristic hpgroup
  let AdditiveRange := (fourAdditiveRange CoefficientRing).toSubgroup
  have hpRange := hpgroup.to_subgroup AdditiveRange
  obtain ⟨rank, hrankCard⟩ := hpRange.exists_card_eq
  apply IsPGroup.of_card (n := rank)
  rw [principal_four_card_eq_additive_range hcharacteristic]
  exact hrankCard

theorem principal_four_normal (CoefficientRing : Type ringUniverse) [Ring CoefficientRing] :
    (principalFourSubgroup CoefficientRing).Normal := by
  constructor
  rintro element ⟨entry, hentry⟩ conjugator
  refine ⟨(conjugator : CoefficientRing) * entry * (conjugator⁻¹ : CoefficientRingˣ).val, ?_⟩
  change (conjugator : CoefficientRing) * element * (conjugator⁻¹ : CoefficientRingˣ).val = _
  rw [hentry]
  calc
    _ = (conjugator : CoefficientRing) * (conjugator⁻¹ : CoefficientRingˣ).val +
      4 * ((conjugator : CoefficientRing) * entry * (conjugator⁻¹ : CoefficientRingˣ).val) := by
        noncomm_ring
    _ = _ := by rw [Units.mul_inv]

theorem principal_involution_subgroup_normal {CoefficientRing : Type ringUniverse}
    [Ring CoefficientRing] {exponent : ℕ} (hcharacteristic : (2 : CoefficientRing) ^ exponent = 0)
    (Action : Subgroup CoefficientRingˣ) :
    ∃ Involutions : Subgroup Action, Involutions.Normal ∧
      CFSG.Open.IsElemAbelian 2 Involutions ∧
      ∀ element : Action, element ∈ Involutions ↔
        element.val ∈ principalFourSubgroup CoefficientRing ∧ element ^ 2 = 1 := by
  let Principal := (principalFourSubgroup CoefficientRing).comap Action.subtype
  let : (principalFourSubgroup CoefficientRing).Normal := principal_four_normal CoefficientRing
  let : Principal.Normal := inferInstance
  have hcommute : ∀ first ∈ Principal, ∀ second ∈ Principal,
      first ^ 2 = 1 → second ^ 2 = 1 → Commute first second := by
    intro first hfirst second hsecond hsquareFirst _
    apply Subtype.ext
    exact principal_involution_central hcharacteristic first.val second.val
      hfirst hsecond (congrArg Subtype.val hsquareFirst)
  let Involutions := normalSquareOneSubgroup Principal hcommute
  refine ⟨Involutions, normalSquareOneSubgroup_normal Principal hcommute,
    normalSquareOneSubgroup_elementary Principal hcommute, ?_⟩
  intro element
  rfl

end CFSG.LargeEvenClassification.Helpers
