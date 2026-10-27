module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicFixedBasisTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem finite_cyclic_zero_fixedBasis_periodic_trace {ring group points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommGroup group] [Finite group]
    [MulAction group points] [Fintype points]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (hgroup : IsPGroup prime group) (element : group)
    (hgenerator : ∀ member : group, ∃ exponent : ℕ, element ^ exponent = member)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End ring (MonoidAlgebra ring points))
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator)
    (hprimaryProjection : Commute projection (Representation.ofMulAction ring group points element))
    (hprimaryOperator : Commute operator (Representation.ofMulAction ring group points element))
    (hzero : permutationFixedBasisReduction (group := group) (IsLocalRing.residue ring) projection = 0) :
    LinearMap.trace ring (MonoidAlgebra ring points)
      (projection * operator * Representation.ofMulAction ring group points element) = 0 := by
  let projector := fun label : ℕ => finiteOrderEigenprojection period periodUnit (root ^ label) operator
  have hrootPeriod : root ^ period = 1 := by
    apply Units.ext
    exact hroot.pow_eq_one
  have heigenvaluePeriod : ∀ label : ℕ, (root ^ label) ^ period = 1 := by
    intro label
    rw [← pow_mul, Nat.mul_comm, pow_mul, hrootPeriod, one_pow]
  have hprojectorIdempotent : ∀ label, IsIdempotentElem (projector label) := by
    intro label
    exact finiteOrderEigenprojection_idempotent period periodUnit (root ^ label) hunit
      (heigenvaluePeriod label) operator hperiod
  have hprojectorCommute : ∀ label, Commute projection (projector label) := by
    intro label
    exact finiteOrderEigenprojection_commute period periodUnit (root ^ label) operator projection hcommute
  have hprojectorPrimary : ∀ label,
      Commute (projector label) (Representation.ofMulAction ring group points element) := by
    intro label
    exact (finiteOrderEigenprojection_commute period periodUnit (root ^ label) operator
      (Representation.ofMulAction ring group points element) hprimaryOperator.symm).symm
  have hprojectorEigenvalue : ∀ label,
      operator * projector label = (↑(root ^ label) : ring) • projector label := by
    intro label
    exact finiteOrderEigenprojection_eigenvalue period periodUnit (root ^ label)
      (heigenvaluePeriod label) operator hperiod
  have hexpansion : projection * operator = ∑ label ∈ Finset.range period,
      (↑(root ^ label) : ring) • (projection * projector label) := by
    calc
      _ = projection * operator * ∑ label ∈ Finset.range period, projector label := by
        rw [finiteOrderEigenprojection_sum period periodUnit root hunit hroot, mul_one]
      _ = ∑ label ∈ Finset.range period, projection * (operator * projector label) := by
        rw [Finset.mul_sum]
        simp only [mul_assoc]
      _ = _ := by simp only [hprojectorEigenvalue, mul_smul_comm]
  have hequivariant : ∀ value : Module.End ring (MonoidAlgebra ring points),
      Commute value (Representation.ofMulAction ring group points element) →
        permutationMapEquivariant (group := group) value := by
    intro value hvalue
    apply permutationMapEquivariant_of_commute
    intro member
    obtain ⟨exponent, hexponent⟩ := hgenerator member
    rw [← hexponent, map_pow]
    exact hvalue.pow_right exponent
  have hprojectedTrace : ∀ label : ℕ, LinearMap.trace ring (MonoidAlgebra ring points)
      ((projection * projector label) * Representation.ofMulAction ring group points element) = 0 := by
    intro label
    have hreduction : permutationFixedBasisReduction (group := group) (IsLocalRing.residue ring)
        (projection * projector label) = 0 := by
      change permutationFixedBasisReduction (group := group) (IsLocalRing.residue ring)
        (projection.comp (projector label)) = 0
      rw [permutationFixedBasisReduction_comp (IsLocalRing.residue ring) prime hgroup projection
        (projector label) (hequivariant projection hprimaryProjection)
        (hequivariant (projector label) (hprojectorPrimary label)), hzero, LinearMap.zero_comp]
    exact finite_cyclic_zero_fixedBasis_trace prime hgroup element hgenerator
      (projection * projector label)
      (IsIdempotentElem.mul_of_commute (hprojectorCommute label) hidempotent (hprojectorIdempotent label))
      (hprimaryProjection.mul_left (hprojectorPrimary label)) hreduction
  rw [hexpansion, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro label _
  rw [smul_mul_assoc, map_smul, hprojectedTrace label, smul_zero]

end CFSG.TwoRankLowerBound.Helpers
