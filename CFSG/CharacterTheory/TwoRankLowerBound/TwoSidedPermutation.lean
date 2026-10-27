module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationCoefficientExtension

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def groupTwoSidedPermutationHom (group : Type*) [Group group] : group × group →* Equiv.Perm group where
  toFun pair :=
    { toFun := fun element => pair.1 * element * pair.2⁻¹
      invFun := fun element => pair.1⁻¹ * element * pair.2
      left_inv := by intro element; group
      right_inv := by intro element; group }
  map_one' := by apply Equiv.ext; intro element; simp
  map_mul' := by
    intro left right
    apply Equiv.ext
    intro element
    change (left.1 * right.1) * element * (left.2 * right.2)⁻¹ =
      left.1 * (right.1 * element * right.2⁻¹) * left.2⁻¹
    group

theorem groupTwoSidedPermutationHom_apply {group : Type*} [Group group] (left right element : group) :
    groupTwoSidedPermutationHom group (left, right) element = left * element * right⁻¹ := rfl

theorem groupTwoSidedPermutation_representation {ring group : Type*} [CommRing ring] [Group group]
    (left right : group) :
    Representation.ofMulAction ring (Equiv.Perm group) group (groupTwoSidedPermutationHom group (left, right)) =
      Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single left 1) *
        LinearMap.mulRight ring (MonoidAlgebra.single right⁻¹ 1) := by
  apply LinearMap.ext
  intro value
  ext element
  rw [Representation.coeff_ofMulAction]
  change value.coeff (left⁻¹ * element * right) =
    (MonoidAlgebra.single left 1 * (value * MonoidAlgebra.single right⁻¹ 1)).coeff element
  simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
    inv_inv, one_mul, mul_one]

theorem central_groupAlgebra_projection_commute_twoSided {ring group : Type*}
    [CommRing ring] [Group group] (coefficient : MonoidAlgebra ring group)
    (hcentral : ∀ other, Commute coefficient other) (left right : group) :
    Commute (Algebra.lmul ring (MonoidAlgebra ring group) coefficient)
      (Representation.ofMulAction ring (Equiv.Perm group) group (groupTwoSidedPermutationHom group (left, right))) := by
  rw [groupTwoSidedPermutation_representation]
  apply Commute.mul_right
  · exact (hcentral (MonoidAlgebra.single left 1)).map (Algebra.lmul ring (MonoidAlgebra ring group))
  · exact LinearMap.commute_mulLeft_right coefficient (MonoidAlgebra.single right⁻¹ 1)

@[expose] noncomputable def liftGroupAlgebraCoefficients {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (coefficient : MonoidAlgebra ℂ group)
    (hintegral : ∀ element, coefficient.coeff element ∈ ring) : MonoidAlgebra ring group :=
  ∑ element : group, MonoidAlgebra.single element ⟨coefficient.coeff element, hintegral element⟩

theorem liftGroupAlgebraCoefficients_map {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (coefficient : MonoidAlgebra ℂ group)
    (hintegral : ∀ element, coefficient.coeff element ∈ ring) :
    MonoidAlgebra.mapRingHom group ring.subtype (liftGroupAlgebraCoefficients ring coefficient hintegral) =
      coefficient := by
  simp only [liftGroupAlgebraCoefficients, map_sum, MonoidAlgebra.mapRingHom_single]
  exact groupAlgebra_sum_single coefficient

theorem groupAlgebraCoefficientEmbedding_injective {group : Type*} [Group group]
    (ring : Subring ℂ) : Function.Injective (MonoidAlgebra.mapRingHom group ring.subtype) := by
  intro left right hequal
  ext element
  have hcoeff := congrArg (fun value : MonoidAlgebra ℂ group => value.coeff element) hequal
  have hequalCoefficient : left.coeff element = right.coeff element :=
    ring.subtype_injective (by simpa only [MonoidAlgebra.coeff_mapRingHom] using hcoeff)
  exact congrArg Subtype.val hequalCoefficient

theorem permutationCoefficientExtension_leftMultiplication {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (coefficient : MonoidAlgebra ring group) :
    permutationCoefficientExtension ring.subtype (Algebra.lmul ring (MonoidAlgebra ring group) coefficient) =
      Algebra.lmul ℂ (MonoidAlgebra ℂ group) (MonoidAlgebra.mapRingHom group ring.subtype coefficient) := by
  apply (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis group ℂ)).injective
  change LinearMap.toMatrix (MonoidAlgebra.basis group ℂ) (MonoidAlgebra.basis group ℂ)
    (permutationCoefficientExtension ring.subtype (Algebra.lmul ring (MonoidAlgebra ring group) coefficient)) =
      LinearMap.toMatrix (MonoidAlgebra.basis group ℂ) (MonoidAlgebra.basis group ℂ)
        (Algebra.lmul ℂ (MonoidAlgebra ℂ group) (MonoidAlgebra.mapRingHom group ring.subtype coefficient))
  rw [permutationCoefficientExtension_matrix, groupAlgebra_leftMultiplicationMatrix_map]

end CFSG.TwoRankLowerBound.Helpers
