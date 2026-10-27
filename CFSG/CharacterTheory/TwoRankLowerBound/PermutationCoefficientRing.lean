module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicPermutationTrace

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem local_residue_prime_complement_unit {ring : Type*} [CommRing ring] [IsLocalRing ring]
    (prime : ℕ) [CharP (IsLocalRing.ResidueField ring) prime] (period : ℕ)
    (hcoprime : ¬ prime ∣ period) : IsUnit (period : ring) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact mt (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ring) prime period).mp hcoprime

theorem complex_subring_primitiveRoot_unit (ring : Subring ℂ) (period : ℕ)
    (hpositive : 0 < period) (hroots : ∀ root : ℂ, root ^ period = 1 → root ∈ ring) :
    ∃ root : ringˣ, IsPrimitiveRoot (root : ring) period := by
  let complexRoot := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / period)
  have hprimitive : IsPrimitiveRoot complexRoot period := Complex.isPrimitiveRoot_exp period
    (Nat.ne_of_gt hpositive)
  let coefficient : ring := ⟨complexRoot, hroots complexRoot hprimitive.pow_eq_one⟩
  have hcoefficient : IsPrimitiveRoot coefficient period := hprimitive.of_map_of_injective ring.subtype_injective
  have hunit := hcoefficient.isUnit (Nat.ne_of_gt hpositive)
  exact ⟨hunit.unit, by rw [hunit.unit_spec]; exact hcoefficient⟩

theorem complex_local_cyclicPermutation_summand_trace_zero (ring : Subring ℂ) [IsLocalRing ring]
    {points : Type*} [Fintype points] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime]
    (primary complement : Equiv.Perm points) (exponent : ℕ)
    (hprimary : orderOf primary = prime ^ exponent)
    (hfixedpointFree : ∀ point : points, primary point ≠ point)
    (hparts : Commute primary complement) (period : ℕ) (hpositive : 0 < period)
    (hcoprime : ¬ prime ∣ period) (hcomplement : complement ^ period = 1)
    (hroots : ∀ root : ℂ, root ^ period = 1 → root ∈ ring)
    (projection : Module.End ring (MonoidAlgebra ring points))
    (hidempotent : IsIdempotentElem projection)
    (hprojectionPrimary : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points primary))
    (hprojectionComplement : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points complement)) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ points)
      (permutationCoefficientExtension ring.subtype projection *
        Representation.ofMulAction ℂ (Equiv.Perm points) points (complement * primary)) = 0 := by
  obtain ⟨root, hroot⟩ := complex_subring_primitiveRoot_unit ring period hpositive hroots
  have hperiodUnit := local_residue_prime_complement_unit prime period hcoprime (ring := ring)
  exact cyclicPermutation_extended_summand_trace_zero ring.subtype prime primary complement exponent
    hprimary hfixedpointFree hparts period hcomplement hperiodUnit.unit root hperiodUnit.unit_spec hroot
    projection hidempotent hprojectionPrimary hprojectionComplement

end CFSG.TwoRankLowerBound.Helpers
