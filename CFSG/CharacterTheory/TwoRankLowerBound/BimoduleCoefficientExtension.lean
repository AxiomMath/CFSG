module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_subgroup_inclusion_map_coefficients {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Fintype group]
    (embedding : ring →+* target) (subgroup : Subgroup group) (value : MonoidAlgebra ring subgroup) :
    MonoidAlgebra.mapRingHom group embedding (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype value) =
      MonoidAlgebra.mapDomainRingHom target subgroup.subtype (MonoidAlgebra.mapRingHom subgroup embedding value) := by
  ext element
  by_cases hmember : element ∈ subgroup
  · let member : subgroup := ⟨element, hmember⟩
    change (MonoidAlgebra.mapRingHom group embedding
      (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype value)).coeff member.val =
      (MonoidAlgebra.mapDomainRingHom target subgroup.subtype
        (MonoidAlgebra.mapRingHom subgroup embedding value)).coeff member.val
    rw [MonoidAlgebra.coeff_mapRingHom, groupAlgebra_subgroup_inclusion_coeff,
      groupAlgebra_subgroup_inclusion_coeff, MonoidAlgebra.coeff_mapRingHom]
  · rw [MonoidAlgebra.coeff_mapRingHom, groupAlgebra_subgroup_inclusion_coeff_zero _ _ _ hmember,
      groupAlgebra_subgroup_inclusion_coeff_zero _ _ _ hmember, map_zero]

theorem permutationCoefficientExtension_rightMultiplication {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (coefficient : MonoidAlgebra ring group) :
    permutationCoefficientExtension ring.subtype (LinearMap.mulRight ring coefficient) =
      LinearMap.mulRight ℂ (MonoidAlgebra.mapRingHom group ring.subtype coefficient) := by
  apply (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis group ℂ)).injective
  change LinearMap.toMatrix (MonoidAlgebra.basis group ℂ) (MonoidAlgebra.basis group ℂ)
    (permutationCoefficientExtension ring.subtype (LinearMap.mulRight ring coefficient)) =
      LinearMap.toMatrix (MonoidAlgebra.basis group ℂ) (MonoidAlgebra.basis group ℂ)
        (LinearMap.mulRight ℂ (MonoidAlgebra.mapRingHom group ring.subtype coefficient))
  rw [permutationCoefficientExtension_matrix]
  ext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis_apply, monoidAlgebra_basis_repr_coeff, LinearMap.mulRight_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, MonoidAlgebra.coeff_mapRingHom]

theorem permutationCoefficientExtension_subgroupBimodule {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (subgroup : Subgroup group) (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring subgroup) :
    permutationCoefficientExtension ring.subtype (subgroupBimoduleProjection subgroup left right) =
      subgroupBimoduleProjection subgroup (MonoidAlgebra.mapRingHom group ring.subtype left)
        (MonoidAlgebra.mapRingHom subgroup ring.subtype right) := by
  change permutationCoefficientExtension ring.subtype
    (Algebra.lmul ring (MonoidAlgebra ring group) left *
      LinearMap.mulRight ring (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right)) = _
  rw [map_mul, permutationCoefficientExtension_leftMultiplication,
    permutationCoefficientExtension_rightMultiplication, groupAlgebra_subgroup_inclusion_map_coefficients]
  rfl

end CFSG.TwoRankLowerBound.Helpers
