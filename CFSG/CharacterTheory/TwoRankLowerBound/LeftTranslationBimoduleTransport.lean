module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def groupAlgebraLeftTranslation {ring group : Type*} [CommRing ring] [Group group]
    (element : group) : MonoidAlgebra ring group ≃ₗ[ring] MonoidAlgebra ring group :=
  LinearEquiv.ofLinearMap
    (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single element 1))
    (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single element⁻¹ 1)) (by
      apply LinearMap.ext
      intro value
      change MonoidAlgebra.single element 1 * (MonoidAlgebra.single element⁻¹ 1 * value) = value
      rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel,
        ← MonoidAlgebra.one_def, one_mul]) (by
      apply LinearMap.ext
      intro value
      change MonoidAlgebra.single element⁻¹ 1 * (MonoidAlgebra.single element 1 * value) = value
      rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul, inv_mul_cancel,
        ← MonoidAlgebra.one_def, one_mul])

theorem groupAlgebraLeftTranslation_conjugate_bimodule {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1)) (conjugator : group) :
    (LinearEquiv.conjAlgEquiv ring (groupAlgebraLeftTranslation (ring := ring) conjugator))
      (subgroupBimoduleProjection subgroup left right) = subgroupBimoduleProjection subgroup left right := by
  apply LinearMap.ext
  intro value
  rw [LinearEquiv.conjAlgEquiv_apply_apply, subgroupBimoduleProjection_apply,
    subgroupBimoduleProjection_apply]
  change MonoidAlgebra.single conjugator 1 * (left *
    (MonoidAlgebra.single conjugator⁻¹ 1 * value) *
      MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right) = _
  calc
    _ = (MonoidAlgebra.single conjugator 1 * left) * MonoidAlgebra.single conjugator⁻¹ 1 * value *
        MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right := by simp only [mul_assoc]
    _ = (left * MonoidAlgebra.single conjugator 1) * MonoidAlgebra.single conjugator⁻¹ 1 * value *
        MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right := by rw [(hleft conjugator).eq]
    _ = _ := by
      rw [mul_assoc left, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel,
        ← MonoidAlgebra.one_def, mul_one]

theorem groupAlgebraLeftTranslation_conjugate_twoSided {ring group : Type*}
    [CommRing ring] [Group group] (left right conjugator : group) :
    (LinearEquiv.conjAlgEquiv ring (groupAlgebraLeftTranslation (ring := ring) conjugator))
      (Representation.ofMulAction ring (Equiv.Perm group) group
        (groupTwoSidedPermutationHom group (left, right))) =
      Representation.ofMulAction ring (Equiv.Perm group) group
        (groupTwoSidedPermutationHom group (conjugator * left * conjugator⁻¹, right)) := by
  rw [groupTwoSidedPermutation_representation, groupTwoSidedPermutation_representation]
  apply LinearMap.ext
  intro value
  change MonoidAlgebra.single conjugator 1 *
    (MonoidAlgebra.single left 1 * ((MonoidAlgebra.single conjugator⁻¹ 1 * value) *
      MonoidAlgebra.single right⁻¹ 1)) =
    MonoidAlgebra.single (conjugator * left * conjugator⁻¹) 1 * (value * MonoidAlgebra.single right⁻¹ 1)
  calc
    _ = (MonoidAlgebra.single conjugator 1 * MonoidAlgebra.single left 1 *
        MonoidAlgebra.single conjugator⁻¹ 1) * (value * MonoidAlgebra.single right⁻¹ 1) := by
          simp only [mul_assoc]
    _ = _ := by rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, one_mul]

theorem subgroupBimodule_twoSided_trace_conjugate_left {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1))
    (leftElement rightElement conjugator : group) :
    LinearMap.trace ring (MonoidAlgebra ring group)
      (subgroupBimoduleProjection subgroup left right *
        Representation.ofMulAction ring (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (conjugator * leftElement * conjugator⁻¹, rightElement))) =
      LinearMap.trace ring (MonoidAlgebra ring group)
        (subgroupBimoduleProjection subgroup left right *
          Representation.ofMulAction ring (Equiv.Perm group) group
            (groupTwoSidedPermutationHom group (leftElement, rightElement))) := by
  have hequal := LinearMap.trace_conj'
    (subgroupBimoduleProjection subgroup left right *
      Representation.ofMulAction ring (Equiv.Perm group) group
        (groupTwoSidedPermutationHom group (leftElement, rightElement)))
    (groupAlgebraLeftTranslation (ring := ring) conjugator)
  change LinearMap.trace ring _
    ((LinearEquiv.conjAlgEquiv ring (groupAlgebraLeftTranslation (ring := ring) conjugator))
      (subgroupBimoduleProjection subgroup left right *
        Representation.ofMulAction ring (Equiv.Perm group) group
          (groupTwoSidedPermutationHom group (leftElement, rightElement)))) = _ at hequal
  rw [map_mul, groupAlgebraLeftTranslation_conjugate_bimodule subgroup left right hleft,
    groupAlgebraLeftTranslation_conjugate_twoSided] at hequal
  exact hequal

end CFSG.TwoRankLowerBound.Helpers
