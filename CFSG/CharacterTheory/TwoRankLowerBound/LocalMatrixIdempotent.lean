module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationCoefficientExtension

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem local_matrix_isUnit_iff_residue {ring index : Type*}
    [CommRing ring] [IsLocalRing ring] [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ring) :
    IsUnit ((IsLocalRing.residue ring).mapMatrix matrix) ↔ IsUnit matrix := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    ← RingHom.map_det, isUnit_iff_ne_zero, IsLocalRing.residue_ne_zero_iff_isUnit]

theorem local_matrix_one_sub_isUnit_of_residue_zero {ring index : Type*}
    [CommRing ring] [IsLocalRing ring] [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ring)
    (hzero : (IsLocalRing.residue ring).mapMatrix matrix = 0) :
    IsUnit (1 - matrix) := by
  apply (local_matrix_isUnit_iff_residue (1 - matrix)).mp
  rw [map_sub, map_one, hzero, sub_zero]
  exact isUnit_one

theorem local_matrix_idempotent_eq_zero_of_residue_zero {ring index : Type*}
    [CommRing ring] [IsLocalRing ring] [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ring) (hidempotent : IsIdempotentElem matrix)
    (hzero : (IsLocalRing.residue ring).mapMatrix matrix = 0) : matrix = 0 := by
  have hunit := local_matrix_one_sub_isUnit_of_residue_zero matrix hzero
  have hequal : (1 - matrix) * matrix = (1 - matrix) * 0 := by
    rw [sub_mul, one_mul, hidempotent.eq, sub_self, mul_zero]
  exact hunit.mul_left_cancel hequal

theorem local_permutation_one_sub_isUnit_of_residue_zero {ring points : Type*}
    [CommRing ring] [IsLocalRing ring] [Fintype points]
    (operator : Module.End ring (MonoidAlgebra ring points))
    (hzero : permutationCoefficientExtension (IsLocalRing.residue ring) operator = 0) :
    IsUnit (1 - operator) := by
  let equivalence := LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis points ring)
  have hmatrix : (IsLocalRing.residue ring).mapMatrix (equivalence operator) = 0 := by
    have hequal := permutationCoefficientExtension_matrix (IsLocalRing.residue ring) operator
    rw [hzero, map_zero] at hequal
    exact hequal.symm
  have hunit := local_matrix_one_sub_isUnit_of_residue_zero (equivalence operator) hmatrix
  rw [← map_one equivalence, ← map_sub equivalence] at hunit
  exact (MulEquiv.isUnit_map equivalence).mp hunit

end CFSG.TwoRankLowerBound.Helpers
