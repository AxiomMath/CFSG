module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem algebraicInteger_prime_complement_complex_unit
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (denominator : ideal.primeCompl) : IsUnit (denominator.val.val : ℂ) := by
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hequal : denominator.val = 0 := Subtype.ext hzero
  exact denominator.property (hequal ▸ ideal.zero_mem)

@[expose] noncomputable def localizedAlgebraicIntegerEmbedding
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] : Localization.AtPrime ideal →+* ℂ :=
  IsLocalization.lift (g := (integralClosure ℤ ℂ).val.toRingHom)
    (algebraicInteger_prime_complement_complex_unit ideal)

theorem localizedAlgebraicIntegerEmbedding_constant
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (integer : ComplexAlgebraicIntegers) :
    localizedAlgebraicIntegerEmbedding ideal
      (algebraMap ComplexAlgebraicIntegers (Localization.AtPrime ideal) integer) = integer.val := by
  exact IsLocalization.lift_eq _ integer

theorem localizedAlgebraicIntegerEmbedding_injective
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] :
    Function.Injective (localizedAlgebraicIntegerEmbedding ideal) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := ideal.primeCompl)
    (Localization.AtPrime ideal)
  intro integer hzero
  rw [localizedAlgebraicIntegerEmbedding_constant] at hzero
  have hequal : integer = 0 := Subtype.ext hzero
  rw [hequal, map_zero]

@[expose] noncomputable def localizedComplexIntegerRing
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] : Subring ℂ :=
  (localizedAlgebraicIntegerEmbedding ideal).range

@[expose] noncomputable def localizedComplexIntegerEquiv
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] :
    Localization.AtPrime ideal ≃+* localizedComplexIntegerRing ideal :=
  RingEquiv.ofBijective (localizedAlgebraicIntegerEmbedding ideal).rangeRestrict
    ⟨fun _ _ hequal => localizedAlgebraicIntegerEmbedding_injective ideal
      (congrArg Subtype.val hequal), (localizedAlgebraicIntegerEmbedding ideal).rangeRestrict_surjective⟩

instance localizedComplexIntegerRing_isLocalRing
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] :
    IsLocalRing (localizedComplexIntegerRing ideal) :=
  (localizedComplexIntegerEquiv ideal).isLocalRing

theorem algebraicInteger_prime_complement_residue_unit
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (denominator : ideal.primeCompl) :
    IsUnit (Ideal.Quotient.mk ideal denominator.val) := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  exact denominator.property (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

@[expose] noncomputable def localizedAlgebraicIntegerResidue
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    Localization.AtPrime ideal →+* ComplexAlgebraicIntegers ⧸ ideal :=
  IsLocalization.lift (g := Ideal.Quotient.mk ideal)
    (algebraicInteger_prime_complement_residue_unit ideal)

theorem localizedAlgebraicIntegerResidue_constant
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (integer : ComplexAlgebraicIntegers) :
    localizedAlgebraicIntegerResidue ideal
      (algebraMap ComplexAlgebraicIntegers (Localization.AtPrime ideal) integer) =
      Ideal.Quotient.mk ideal integer := by
  exact IsLocalization.lift_eq _ integer

theorem localizedAlgebraicIntegerResidue_surjective
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    Function.Surjective (localizedAlgebraicIntegerResidue ideal) := by
  intro residue
  obtain ⟨integer, rfl⟩ := Ideal.Quotient.mk_surjective residue
  exact ⟨algebraMap ComplexAlgebraicIntegers (Localization.AtPrime ideal) integer,
    localizedAlgebraicIntegerResidue_constant ideal integer⟩

@[expose] noncomputable def localizedComplexIntegerResidue
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    localizedComplexIntegerRing ideal →+* ComplexAlgebraicIntegers ⧸ ideal :=
  (localizedAlgebraicIntegerResidue ideal).comp (localizedComplexIntegerEquiv ideal).symm.toRingHom

theorem localizedComplexIntegerResidue_surjective
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    Function.Surjective (localizedComplexIntegerResidue ideal) :=
  (localizedAlgebraicIntegerResidue_surjective ideal).comp
    (localizedComplexIntegerEquiv ideal).symm.surjective

theorem complexAlgebraicInteger_mem_localized_ring
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (integer : ComplexAlgebraicIntegers) :
    integer.val ∈ localizedComplexIntegerRing ideal := by
  exact ⟨algebraMap ComplexAlgebraicIntegers (Localization.AtPrime ideal) integer,
    localizedAlgebraicIntegerEmbedding_constant ideal integer⟩

theorem localizedAlgebraicIntegerEmbedding_fraction
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (numerator : ComplexAlgebraicIntegers) (denominator : ideal.primeCompl) :
    localizedAlgebraicIntegerEmbedding ideal
      (IsLocalization.mk' (Localization.AtPrime ideal) numerator denominator) =
      numerator.val / denominator.val.val := by
  have hspec := congrArg (localizedAlgebraicIntegerEmbedding ideal)
    (IsLocalization.mk'_spec (Localization.AtPrime ideal) numerator denominator)
  rw [map_mul, localizedAlgebraicIntegerEmbedding_constant,
    localizedAlgebraicIntegerEmbedding_constant] at hspec
  exact (eq_div_iff (isUnit_iff_ne_zero.mp
    (algebraicInteger_prime_complement_complex_unit ideal denominator))).mpr hspec

theorem localizedComplexIntegerRing_mem_iff_fraction
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (value : ℂ) :
    value ∈ localizedComplexIntegerRing ideal ↔
      ∃ (numerator denominator : ComplexAlgebraicIntegers), denominator ∉ ideal ∧
        value = numerator.val / denominator.val := by
  constructor
  · rintro ⟨preimage, rfl⟩
    obtain ⟨numerator, denominator, rfl⟩ := IsLocalization.exists_mk'_eq ideal.primeCompl preimage
    exact ⟨numerator, denominator.val, denominator.property,
      localizedAlgebraicIntegerEmbedding_fraction ideal numerator denominator⟩
  · rintro ⟨numerator, denominator, hdenominator, rfl⟩
    exact ⟨IsLocalization.mk' (Localization.AtPrime ideal) numerator ⟨denominator, hdenominator⟩,
      localizedAlgebraicIntegerEmbedding_fraction ideal numerator ⟨denominator, hdenominator⟩⟩

theorem localizedAlgebraicIntegerResidue_fraction
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (numerator : ComplexAlgebraicIntegers) (denominator : ideal.primeCompl) :
    letI : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
    localizedAlgebraicIntegerResidue ideal
      (IsLocalization.mk' (Localization.AtPrime ideal) numerator denominator) =
      Ideal.Quotient.mk ideal numerator / Ideal.Quotient.mk ideal denominator.val := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  have hspec := congrArg (localizedAlgebraicIntegerResidue ideal)
    (IsLocalization.mk'_spec (Localization.AtPrime ideal) numerator denominator)
  rw [map_mul, localizedAlgebraicIntegerResidue_constant,
    localizedAlgebraicIntegerResidue_constant] at hspec
  exact (eq_div_iff (fun hzero => denominator.property
    (Ideal.Quotient.eq_zero_iff_mem.mp hzero))).mpr hspec

theorem localizedAlgebraicIntegerResidue_fraction_zero_iff
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (numerator : ComplexAlgebraicIntegers) (denominator : ideal.primeCompl) :
    localizedAlgebraicIntegerResidue ideal
      (IsLocalization.mk' (Localization.AtPrime ideal) numerator denominator) = 0 ↔ numerator ∈ ideal := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  rw [localizedAlgebraicIntegerResidue_fraction, div_eq_zero_iff]
  have hdenominator : Ideal.Quotient.mk ideal denominator.val ≠ 0 :=
    fun hzero => denominator.property (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  simp only [hdenominator, or_false, Ideal.Quotient.eq_zero_iff_mem]

theorem localizedComplexIntegerResidue_isUnit_iff
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : localizedComplexIntegerRing ideal) :
    IsUnit value ↔ localizedComplexIntegerResidue ideal value ≠ 0 := by
  let preimage := (localizedComplexIntegerEquiv ideal).symm value
  have hunit : IsUnit value ↔ IsUnit preimage := by
    constructor
    · exact fun hvalue => hvalue.map (localizedComplexIntegerEquiv ideal).symm.toMonoidHom
    · intro hpreimage
      have hvalue := hpreimage.map (localizedComplexIntegerEquiv ideal).toMonoidHom
      change IsUnit ((localizedComplexIntegerEquiv ideal)
        ((localizedComplexIntegerEquiv ideal).symm value)) at hvalue
      simpa only [RingEquiv.apply_symm_apply] using hvalue
  rw [hunit]
  change IsUnit preimage ↔ localizedAlgebraicIntegerResidue ideal preimage ≠ 0
  obtain ⟨numerator, denominator, hequal⟩ := IsLocalization.exists_mk'_eq ideal.primeCompl preimage
  rw [← hequal]
  rw [IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime ideal) ideal,
    ne_eq, localizedAlgebraicIntegerResidue_fraction_zero_iff]
  rfl

theorem localizedComplexIntegerResidue_integer
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (integer : ℤ) :
    localizedComplexIntegerResidue ideal (integer : localizedComplexIntegerRing ideal) =
      (integer : ComplexAlgebraicIntegers ⧸ ideal) :=
  map_intCast _ integer

theorem localizedComplexInteger_integer_unit_iff
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (prime : ℕ)
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime] (integer : ℤ) :
    IsUnit (integer : localizedComplexIntegerRing ideal) ↔ ¬(prime : ℤ) ∣ integer := by
  rw [localizedComplexIntegerResidue_isUnit_iff, localizedComplexIntegerResidue_integer,
    ne_eq, CharP.intCast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) prime]

theorem localizedComplexIntegerResidue_kernel_maximal
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    (RingHom.ker (localizedComplexIntegerResidue ideal)).IsMaximal := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  exact RingHom.ker_isMaximal_of_surjective _ (localizedComplexIntegerResidue_surjective ideal)

end CFSG.TwoRankLowerBound.Helpers
