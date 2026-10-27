module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationTraceVanishing

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def permutationCoefficientExtension {ring target points : Type*}
    [CommRing ring] [CommRing target] [Fintype points] (embedding : ring →+* target) :
    Module.End ring (MonoidAlgebra ring points) →+* Module.End target (MonoidAlgebra target points) :=
  (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points target)).symm.toRingHom.comp
    (embedding.mapMatrix.comp
      (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points ring)).toRingHom)

theorem permutationCoefficientExtension_matrix {ring target points : Type*}
    [CommRing ring] [CommRing target] [Fintype points] (embedding : ring →+* target)
    (operator : Module.End ring (MonoidAlgebra ring points)) :
    LinearMap.toMatrix (MonoidAlgebra.basis points target) (MonoidAlgebra.basis points target)
      (permutationCoefficientExtension embedding operator) =
      embedding.mapMatrix (LinearMap.toMatrix (MonoidAlgebra.basis points ring)
        (MonoidAlgebra.basis points ring) operator) := by
  change (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points target))
    ((LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points target)).symm
      (embedding.mapMatrix ((LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points ring)) operator))) = _
  exact (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points target)).apply_symm_apply _

theorem permutationCoefficientExtension_trace {ring target points : Type*}
    [CommRing ring] [CommRing target] [Fintype points] (embedding : ring →+* target)
    (operator : Module.End ring (MonoidAlgebra ring points)) :
    LinearMap.trace target (MonoidAlgebra target points) (permutationCoefficientExtension embedding operator) =
      embedding (LinearMap.trace ring (MonoidAlgebra ring points) operator) := by
  rw [LinearMap.trace_eq_matrix_trace target (MonoidAlgebra.basis points target),
    permutationCoefficientExtension_matrix,
    LinearMap.trace_eq_matrix_trace ring (MonoidAlgebra.basis points ring)]
  simp only [Matrix.trace, RingHom.mapMatrix_apply, Matrix.diag_map, map_sum]
  rfl

theorem permutationCoefficientExtension_translation {ring target group points : Type*}
    [CommRing ring] [CommRing target] [Group group] [MulAction group points] [Fintype points]
    (embedding : ring →+* target) (element : group) :
    permutationCoefficientExtension embedding (Representation.ofMulAction ring group points element) =
      Representation.ofMulAction target group points element := by
  apply (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points target)).injective
  change LinearMap.toMatrix (MonoidAlgebra.basis points target) (MonoidAlgebra.basis points target)
    (permutationCoefficientExtension embedding (Representation.ofMulAction ring group points element)) =
      LinearMap.toMatrix (MonoidAlgebra.basis points target) (MonoidAlgebra.basis points target)
        (Representation.ofMulAction target group points element)
  rw [permutationCoefficientExtension_matrix]
  ext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis_apply]
  change embedding (((Representation.ofMulAction ring group points element)
    (MonoidAlgebra.single column 1)).coeff row) =
      ((Representation.ofMulAction target group points element) (MonoidAlgebra.single column 1)).coeff row
  simp only [Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem finite_p_action_extended_summand_trace_zero {ring target group points : Type*}
    [CommRing ring] [IsDomain ring] [IsLocalRing ring] [CommRing target]
    [CommGroup group] [Finite group] [MulAction group points] [Fintype points]
    (embedding : ring →+* target) (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime] (hgroup : IsPGroup prime group)
    (element : group) (hfixedpointFree : ∀ point : points, element • point ≠ point)
    (period : ℕ) (periodUnit root : ringˣ) (hunit : (periodUnit : ring) = period)
    (hroot : IsPrimitiveRoot (root : ring) period)
    (operator projection : Module.End ring (MonoidAlgebra ring points))
    (hoperator : ∀ member : group, Commute operator (Representation.ofMulAction ring group points member))
    (hprojection : ∀ member : group, Commute projection (Representation.ofMulAction ring group points member))
    (hperiod : operator ^ period = 1) (hidempotent : IsIdempotentElem projection)
    (hcommute : Commute projection operator) :
    LinearMap.trace target (MonoidAlgebra target points)
      (permutationCoefficientExtension embedding projection * permutationCoefficientExtension embedding operator *
        Representation.ofMulAction target group points element) = 0 := by
  rw [← permutationCoefficientExtension_translation embedding element, ← map_mul, ← map_mul,
    permutationCoefficientExtension_trace,
    finite_p_action_equivariant_summand_trace_zero prime hgroup element hfixedpointFree
      period periodUnit root hunit hroot operator projection hoperator hprojection hperiod hidempotent hcommute,
    map_zero]

end CFSG.TwoRankLowerBound.Helpers
