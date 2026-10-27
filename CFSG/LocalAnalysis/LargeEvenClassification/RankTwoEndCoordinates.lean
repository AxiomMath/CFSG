module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCoordinateMaps
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Basify

public section

namespace CFSG.LargeEvenClassification.Helpers

abbrev CyclicPair (scale modulus : ℕ) := ZMod (scale * modulus) × ZMod modulus

abbrev CyclicPairCoefficients (scale modulus : ℕ) :=
  (ZMod (scale * modulus) × ZMod modulus) × (ZMod modulus × ZMod modulus)

section Coordinates

variable (scale modulus : ℕ) [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)]

omit [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)] in
theorem cyclicPairEnd_upper_right_annihilated (operator : AddMonoid.End (CyclicPair scale modulus)) :
    (modulus : ZMod (scale * modulus)) * (operator (0, 1)).1 = 0 := by
  let homomorphism := (AddMonoidHom.fst _ _).comp
    ((AddMonoid.End.equiv _ operator).comp (AddMonoidHom.inr _ _))
  have hzero : modulus • (1 : ZMod modulus) = 0 := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  have heq := congrArg homomorphism hzero
  rw [map_nsmul, map_zero] at heq
  change modulus • (operator (0, 1)).1 = 0 at heq
  simpa only [nsmul_eq_mul] using heq

@[expose] noncomputable def cyclicPairEndCoefficients (operator : AddMonoid.End (CyclicPair scale modulus)) :
    CyclicPairCoefficients scale modulus :=
  (((operator (1, 0)).1, Classical.choose (scaledCyclicInclusion_range scale modulus
    (NeZero.pos scale) (operator (0, 1)).1
    (cyclicPairEnd_upper_right_annihilated scale modulus operator))),
    ((operator (1, 0)).2, (operator (0, 1)).2))

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_upper_right
    (operator : AddMonoid.End (CyclicPair scale modulus)) :
    scaledCyclicInclusion scale modulus (cyclicPairEndCoefficients scale modulus operator).1.2 =
      (operator (0, 1)).1 :=
  Classical.choose_spec (scaledCyclicInclusion_range scale modulus (NeZero.pos scale)
    (operator (0, 1)).1 (cyclicPairEnd_upper_right_annihilated scale modulus operator))

theorem cyclicPairEnd_apply (operator : AddMonoid.End (CyclicPair scale modulus))
    (element : CyclicPair scale modulus) :
    operator element =
      ((cyclicPairEndCoefficients scale modulus operator).1.1 * element.1 +
        scaledCyclicInclusion scale modulus
          ((cyclicPairEndCoefficients scale modulus operator).1.2 * element.2),
        (cyclicPairEndCoefficients scale modulus operator).2.1 *
          cyclicReduction scale modulus element.1 +
          (cyclicPairEndCoefficients scale modulus operator).2.2 * element.2) := by
  have hfirst : element.1.val • ((1, 0) : CyclicPair scale modulus) = (element.1, 0) := by
    apply Prod.ext
    · change element.1.val • (1 : ZMod (scale * modulus)) = element.1
      simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val element.1
    · simp
  have hsecond : element.2.val • ((0, 1) : CyclicPair scale modulus) = (0, element.2) := by
    apply Prod.ext
    · simp
    · change element.2.val • (1 : ZMod modulus) = element.2
      simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val element.2
  have hsplit : element = element.1.val • ((1, 0) : CyclicPair scale modulus) +
      element.2.val • ((0, 1) : CyclicPair scale modulus) := by
    rw [hfirst, hsecond]
    simp
  calc
    operator element = element.1.val • operator (1, 0) + element.2.val • operator (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_nsmul, map_nsmul]
    _ = _ := by
      apply Prod.ext
      · change element.1.val • (operator (1, 0)).1 + element.2.val • (operator (0, 1)).1 = _
        rw [← cyclicPairEndCoefficients_upper_right scale modulus operator,
          ← map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val,
          ZMod.natCast_zmod_val]
        change _ * (cyclicPairEndCoefficients scale modulus operator).1.1 +
          scaledCyclicInclusion scale modulus (_ * _) = _
        rw [mul_comm element.1, mul_comm element.2]
      · change element.1.val • (operator (1, 0)).2 + element.2.val • (operator (0, 1)).2 = _
        rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val,
          ← cyclicReduction_apply scale modulus element.1]
        change _ * (cyclicPairEndCoefficients scale modulus operator).2.1 +
          _ * (cyclicPairEndCoefficients scale modulus operator).2.2 = _
        rw [mul_comm (cyclicReduction scale modulus element.1), mul_comm element.2]

@[expose] def cyclicPairEndFromCoefficients (coefficients : CyclicPairCoefficients scale modulus) :
    AddMonoid.End (CyclicPair scale modulus) :=
  (AddMonoid.End.equiv _).symm {
    toFun := fun element =>
      (coefficients.1.1 * element.1 + scaledCyclicInclusion scale modulus (coefficients.1.2 * element.2),
        coefficients.2.1 * cyclicReduction scale modulus element.1 + coefficients.2.2 * element.2)
    map_zero' := by simp
    map_add' := by
      intro first second
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add] <;> abel }

omit [NeZero scale] [NeZero modulus] [NeZero (scale * modulus)] in
theorem cyclicPairEndFromCoefficients_apply (coefficients : CyclicPairCoefficients scale modulus)
    (element : CyclicPair scale modulus) :
    cyclicPairEndFromCoefficients scale modulus coefficients element =
      (coefficients.1.1 * element.1 + scaledCyclicInclusion scale modulus (coefficients.1.2 * element.2),
        coefficients.2.1 * cyclicReduction scale modulus element.1 + coefficients.2.2 * element.2) := rfl

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_from (coefficients : CyclicPairCoefficients scale modulus) :
    cyclicPairEndCoefficients scale modulus (cyclicPairEndFromCoefficients scale modulus coefficients) =
      coefficients := by
  apply Prod.ext
  · apply Prod.ext
    · change coefficients.1.1 * 1 + scaledCyclicInclusion scale modulus (coefficients.1.2 * 0) = _
      simp
    · apply scaledCyclicInclusion_injective scale modulus (NeZero.pos scale)
      rw [cyclicPairEndCoefficients_upper_right, cyclicPairEndFromCoefficients_apply]
      simp
  · apply Prod.ext
    · change coefficients.2.1 * cyclicReduction scale modulus 1 + coefficients.2.2 * 0 = _
      simp
    · change coefficients.2.1 * cyclicReduction scale modulus 0 + coefficients.2.2 * 1 = _
      simp

theorem cyclicPairEnd_from_coefficients (operator : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndFromCoefficients scale modulus (cyclicPairEndCoefficients scale modulus operator) =
      operator := by
  apply AddMonoid.End.ext
  intro element
  exact (cyclicPairEnd_apply scale modulus operator element).symm

theorem cyclicPairEndCoefficients_injective :
    Function.Injective (cyclicPairEndCoefficients scale modulus) := by
  intro first second heq
  rw [← cyclicPairEnd_from_coefficients scale modulus first,
    ← cyclicPairEnd_from_coefficients scale modulus second, heq]

@[expose] noncomputable def cyclicPairEndCoefficientEquiv :
    AddMonoid.End (CyclicPair scale modulus) ≃ CyclicPairCoefficients scale modulus where
  toFun := cyclicPairEndCoefficients scale modulus
  invFun := cyclicPairEndFromCoefficients scale modulus
  left_inv := cyclicPairEnd_from_coefficients scale modulus
  right_inv := cyclicPairEndCoefficients_from scale modulus

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_one :
    cyclicPairEndCoefficients scale modulus 1 = ((1, 0), (0, 1)) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply scaledCyclicInclusion_injective scale modulus (NeZero.pos scale)
      change scaledCyclicInclusion scale modulus (cyclicPairEndCoefficients scale modulus 1).1.2 =
        scaledCyclicInclusion scale modulus 0
      rw [cyclicPairEndCoefficients_upper_right, map_zero]
      rfl
  · apply Prod.ext <;> rfl

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_add (first second : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndCoefficients scale modulus (first + second) =
      cyclicPairEndCoefficients scale modulus first + cyclicPairEndCoefficients scale modulus second := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply scaledCyclicInclusion_injective scale modulus (NeZero.pos scale)
      change scaledCyclicInclusion scale modulus (cyclicPairEndCoefficients scale modulus (first + second)).1.2 =
        scaledCyclicInclusion scale modulus ((cyclicPairEndCoefficients scale modulus first).1.2 +
          (cyclicPairEndCoefficients scale modulus second).1.2)
      rw [map_add, cyclicPairEndCoefficients_upper_right, cyclicPairEndCoefficients_upper_right,
        cyclicPairEndCoefficients_upper_right]
      rfl
  · apply Prod.ext <;> rfl

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_zero :
    cyclicPairEndCoefficients scale modulus 0 = 0 := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply scaledCyclicInclusion_injective scale modulus (NeZero.pos scale)
      change scaledCyclicInclusion scale modulus (cyclicPairEndCoefficients scale modulus 0).1.2 =
        scaledCyclicInclusion scale modulus 0
      rw [cyclicPairEndCoefficients_upper_right, map_zero]
      rfl
  · apply Prod.ext <;> rfl

@[expose] noncomputable def cyclicPairEndCoefficientHom :
    AddMonoid.End (CyclicPair scale modulus) →+ CyclicPairCoefficients scale modulus where
  toFun := cyclicPairEndCoefficients scale modulus
  map_zero' := cyclicPairEndCoefficients_zero scale modulus
  map_add' := cyclicPairEndCoefficients_add scale modulus

omit [NeZero (scale * modulus)] in
theorem cyclicPairEndCoefficients_nsmul (scalar : ℕ)
    (operator : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndCoefficients scale modulus (scalar • operator) =
      scalar • cyclicPairEndCoefficients scale modulus operator :=
  map_nsmul (cyclicPairEndCoefficientHom scale modulus) scalar operator

@[expose] def cyclicPairCoefficientProduct (first second : CyclicPairCoefficients scale modulus) :
    CyclicPairCoefficients scale modulus :=
  ((first.1.1 * second.1.1 + scaledCyclicInclusion scale modulus (first.1.2 * second.2.1),
    cyclicReduction scale modulus first.1.1 * second.1.2 + first.1.2 * second.2.2),
    (first.2.1 * cyclicReduction scale modulus second.1.1 + first.2.2 * second.2.1,
      (scale : ZMod modulus) * first.2.1 * second.1.2 + first.2.2 * second.2.2))

theorem cyclicPairEndCoefficients_mul (first second : AddMonoid.End (CyclicPair scale modulus)) :
    cyclicPairEndCoefficients scale modulus (first * second) =
      cyclicPairCoefficientProduct scale modulus (cyclicPairEndCoefficients scale modulus first)
        (cyclicPairEndCoefficients scale modulus second) := by
  have hfirst := cyclicPairEnd_apply scale modulus first (second (1, 0))
  have hsecond := cyclicPairEnd_apply scale modulus first (second (0, 1))
  apply Prod.ext
  · apply Prod.ext
    · change (first (second (1, 0))).1 =
        (cyclicPairEndCoefficients scale modulus first).1.1 * (second (1, 0)).1 +
          scaledCyclicInclusion scale modulus
            ((cyclicPairEndCoefficients scale modulus first).1.2 * (second (1, 0)).2)
      exact congrArg (fun element : CyclicPair scale modulus => element.1) hfirst
    · apply scaledCyclicInclusion_injective scale modulus (NeZero.pos scale)
      rw [cyclicPairEndCoefficients_upper_right]
      change (first (second (0, 1))).1 = scaledCyclicInclusion scale modulus
        (cyclicReduction scale modulus (cyclicPairEndCoefficients scale modulus first).1.1 *
          (cyclicPairEndCoefficients scale modulus second).1.2 +
          (cyclicPairEndCoefficients scale modulus first).1.2 *
            (cyclicPairEndCoefficients scale modulus second).2.2)
      rw [hsecond, map_add, scaledCyclicInclusion_scalar,
        cyclicPairEndCoefficients_upper_right]
      rfl
  · apply Prod.ext
    · exact congrArg Prod.snd hfirst
    · change (first (second (0, 1))).2 = _
      rw [hsecond]
      change (cyclicPairEndCoefficients scale modulus first).2.1 *
          cyclicReduction scale modulus (second (0, 1)).1 +
          (cyclicPairEndCoefficients scale modulus first).2.2 * (second (0, 1)).2 = _
      rw [← cyclicPairEndCoefficients_upper_right scale modulus second, cyclicReduction_inclusion]
      change _ = (scale : ZMod modulus) * (cyclicPairEndCoefficients scale modulus first).2.1 *
        (cyclicPairEndCoefficients scale modulus second).1.2 +
        (cyclicPairEndCoefficients scale modulus first).2.2 *
          (cyclicPairEndCoefficients scale modulus second).2.2
      change (cyclicPairEndCoefficients scale modulus first).2.1 *
        ((scale : ZMod modulus) * (cyclicPairEndCoefficients scale modulus second).1.2) +
        (cyclicPairEndCoefficients scale modulus first).2.2 *
          (cyclicPairEndCoefficients scale modulus second).2.2 = _
      ring

end Coordinates

end CFSG.LargeEvenClassification.Helpers
