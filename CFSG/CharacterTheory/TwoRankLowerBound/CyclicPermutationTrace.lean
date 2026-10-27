module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationCoefficientExtension

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem cyclicPermutation_summand_trace_zero {ring points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [Fintype points]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (primary complement : Equiv.Perm points) (exponent : ℕ)
    (hprimary : orderOf primary = prime ^ exponent)
    (hfixedpointFree : ∀ point : points, primary point ≠ point)
    (hparts : Commute primary complement) (period : ℕ) (hcomplement : complement ^ period = 1)
    (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (projection : Module.End ring (MonoidAlgebra ring points))
    (hidempotent : IsIdempotentElem projection)
    (hprojectionPrimary : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points primary))
    (hprojectionComplement : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points complement)) :
    LinearMap.trace ring (MonoidAlgebra ring points)
      (projection * Representation.ofMulAction ring (Equiv.Perm points) points (complement * primary)) = 0 := by
  let group := Subgroup.zpowers primary
  let : CommGroup group := IsCyclic.commGroup
  have hgroup : IsPGroup prime group := IsPGroup.of_card (by rw [Nat.card_zpowers, hprimary])
  let element : group := ⟨primary, Subgroup.mem_zpowers primary⟩
  let representation := Representation.ofMulAction ring (Equiv.Perm points) points
  let operator := representation complement
  have hrepresentation : ∀ member : group,
      Representation.ofMulAction ring group points member = representation member.val := by
    intro member
    apply LinearMap.ext
    intro value
    ext point
    change ((Representation.ofMulAction ring group points member) value).coeff point =
      ((Representation.ofMulAction ring (Equiv.Perm points) points member.val) value).coeff point
    simp only [Representation.coeff_ofMulAction]
    rfl
  have hprojection : ∀ member : group,
      Commute projection (Representation.ofMulAction ring group points member) := by
    intro member
    obtain ⟨power, hmember, hequal⟩ := Finset.mem_image.mp
      (((isOfFinOrder_of_finite primary).mem_zpowers_iff_mem_range_orderOf).mp member.property)
    rw [hrepresentation, ← hequal, map_pow]
    exact hprojectionPrimary.pow_right power
  have hoperator : ∀ member : group,
      Commute operator (Representation.ofMulAction ring group points member) := by
    intro member
    obtain ⟨power, hmember, hequal⟩ := Finset.mem_image.mp
      (((isOfFinOrder_of_finite primary).mem_zpowers_iff_mem_range_orderOf).mp member.property)
    rw [hrepresentation, ← hequal, map_pow]
    exact (hparts.symm.map representation).pow_right power
  have hperiod : operator ^ period = 1 := by
    change (representation complement) ^ period = 1
    rw [← map_pow, hcomplement, map_one]
  have htrace := finite_p_action_equivariant_summand_trace_zero prime hgroup element hfixedpointFree
    period periodUnit root hunit hroot operator projection hoperator hprojection hperiod hidempotent
      hprojectionComplement
  rw [hrepresentation] at htrace
  change LinearMap.trace ring (MonoidAlgebra ring points)
    (projection * representation complement * representation primary) = 0 at htrace
  rw [mul_assoc, ← map_mul] at htrace
  exact htrace

theorem cyclicPermutation_extended_summand_trace_zero {ring target points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommRing target] [Fintype points]
    (embedding : ring →+* target) (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime]
    (primary complement : Equiv.Perm points) (exponent : ℕ)
    (hprimary : orderOf primary = prime ^ exponent)
    (hfixedpointFree : ∀ point : points, primary point ≠ point)
    (hparts : Commute primary complement) (period : ℕ) (hcomplement : complement ^ period = 1)
    (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (projection : Module.End ring (MonoidAlgebra ring points))
    (hidempotent : IsIdempotentElem projection)
    (hprojectionPrimary : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points primary))
    (hprojectionComplement : Commute projection (Representation.ofMulAction ring (Equiv.Perm points) points complement)) :
    LinearMap.trace target (MonoidAlgebra target points)
      (permutationCoefficientExtension embedding projection *
        Representation.ofMulAction target (Equiv.Perm points) points (complement * primary)) = 0 := by
  rw [← permutationCoefficientExtension_translation embedding, ← map_mul,
    permutationCoefficientExtension_trace,
    cyclicPermutation_summand_trace_zero prime primary complement exponent hprimary hfixedpointFree
      hparts period hcomplement periodUnit root hunit hroot projection hidempotent
      hprojectionPrimary hprojectionComplement,
    map_zero]

end CFSG.TwoRankLowerBound.Helpers
