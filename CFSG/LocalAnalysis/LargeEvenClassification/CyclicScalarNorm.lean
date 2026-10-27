module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalar

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem binaryCongruenceInvolution_fixed_square (exponent : ℕ)
    (source : ZMod (2 ^ (exponent + 3)))
    (hfixed : (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * source = source) :
    ∃ root : ZMod (2 ^ (exponent + 3)), root + root = source := by
  let : NeZero (2 ^ (exponent + 3)) := ⟨by positivity⟩
  rw [binaryCongruenceInvolution_val] at hfixed
  have hzero : (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) * source = 0 := by
    linear_combination hfixed
  have hcastZero : ((2 ^ (exponent + 2) * source.val : ℕ) : ZMod (2 ^ (exponent + 3))) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hzero
  have hdivides := (ZMod.natCast_eq_zero_iff _ _).mp hcastZero
  have htwoDivides : 2 ∣ source.val := by
    have hmodulus : 2 ^ (exponent + 3) = 2 ^ (exponent + 2) * 2 := by
      rw [← pow_succ]
    have hrewritten : 2 ^ (exponent + 2) * 2 ∣ 2 ^ (exponent + 2) * source.val :=
      hmodulus ▸ hdivides
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2 ^ (exponent + 2)) hrewritten
  obtain ⟨quotient, hquotient⟩ := htwoDivides
  refine ⟨quotient, ?_⟩
  rw [← ZMod.natCast_zmod_val source, hquotient]
  push_cast
  ring

theorem binaryCongruenceInvolution_norm_square (exponent : ℕ)
    (root : ZMod (2 ^ (exponent + 3))) :
    ∃ source : ZMod (2 ^ (exponent + 3)),
      source + (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * source = root + root := by
  let OddUnit : (ZMod (2 ^ (exponent + 3)))ˣ :=
    ZMod.unitOfCoprime (1 + 2 ^ (exponent + 1)) (by
      apply Nat.Coprime.pow_right
      apply Nat.coprime_two_right.mpr
      exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega)))
  have hunitVal : (OddUnit : ZMod (2 ^ (exponent + 3))) = 1 + 2 ^ (exponent + 1) := by
    change ((1 + 2 ^ (exponent + 1) : ℕ) : ZMod (2 ^ (exponent + 3))) = _
    push_cast
    rfl
  have hnormScalar : 1 + (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) = 2 * OddUnit.val := by
    rw [binaryCongruenceInvolution_val, hunitVal]
    have hpower : (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) = 2 * 2 ^ (exponent + 1) := by
      simp only [pow_succ']
    rw [hpower]
    ring
  refine ⟨(OddUnit⁻¹ : (ZMod (2 ^ (exponent + 3)))ˣ).val * root, ?_⟩
  calc
    (OddUnit⁻¹ : (ZMod (2 ^ (exponent + 3)))ˣ).val * root +
        (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) *
          ((OddUnit⁻¹ : (ZMod (2 ^ (exponent + 3)))ˣ).val * root) =
        (1 + (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3)))) *
          ((OddUnit⁻¹ : (ZMod (2 ^ (exponent + 3)))ˣ).val * root) := by ring
    _ = 2 * root := by
      rw [hnormScalar, ← mul_assoc, mul_assoc 2, Units.mul_inv, mul_one]
    _ = root + root := by ring

theorem cyclic_congruence_fixed_square {Cyclic : Type groupUniverse} [CommGroup Cyclic]
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* Cyclic)
    (automorphism : MulAut Cyclic)
    (hscalar : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) automorphism =
      binaryCongruenceInvolution exponent) (source : Cyclic) (hfixed : automorphism source = source) :
    source ∈ (powMonoidHom 2 : Cyclic →* Cyclic).range := by
  obtain ⟨original, rfl⟩ := coordinates.surjective source
  rw [cyclicScalarAutEquiv_apply, hscalar] at hfixed
  have hfixedScalar : (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * original.toAdd =
      original.toAdd := by
    exact congrArg Multiplicative.toAdd (coordinates.injective hfixed)
  obtain ⟨root, hroot⟩ := binaryCongruenceInvolution_fixed_square exponent original.toAdd hfixedScalar
  refine ⟨coordinates (Multiplicative.ofAdd root), ?_⟩
  change coordinates (Multiplicative.ofAdd root) ^ 2 = coordinates original
  rw [← map_pow]
  apply congrArg coordinates
  rw [pow_two]
  change Multiplicative.ofAdd (root + root) = original
  rw [hroot]
  rfl

theorem cyclic_congruence_norm_surjective {Cyclic : Type groupUniverse} [CommGroup Cyclic]
    (exponent : ℕ) (coordinates : Multiplicative (ZMod (2 ^ (exponent + 3))) ≃* Cyclic)
    (automorphism : MulAut Cyclic)
    (hscalar : (cyclicScalarAutEquiv (2 ^ (exponent + 3)) coordinates) automorphism =
      binaryCongruenceInvolution exponent) :
    ∀ square : (powMonoidHom 2 : Cyclic →* Cyclic).range,
      ∃ source : Cyclic, source * automorphism source = square.val := by
  intro square
  obtain ⟨root, hroot⟩ := square.property
  obtain ⟨original, rfl⟩ := coordinates.surjective root
  obtain ⟨source, hnorm⟩ := binaryCongruenceInvolution_norm_square exponent original.toAdd
  refine ⟨coordinates (Multiplicative.ofAdd source), ?_⟩
  rw [cyclicScalarAutEquiv_apply, hscalar, ← map_mul]
  change coordinates (Multiplicative.ofAdd
    (source + (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) * source)) = square.val
  rw [hnorm]
  have hcoordinates : coordinates (Multiplicative.ofAdd (original.toAdd + original.toAdd)) =
      coordinates original ^ 2 := by
    rw [← map_pow]
    simp only [pow_two]
    rfl
  exact hcoordinates.trans hroot

end CFSG.LargeEvenClassification.Helpers
