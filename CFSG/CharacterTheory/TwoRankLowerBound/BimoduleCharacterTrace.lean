module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSummandBimoduleTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionConvolution

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem subgroupBimoduleProjection_expansion {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup) :
    subgroupBimoduleProjection subgroup left right =
      ∑ member : subgroup, right.coeff member •
        subgroupBimoduleProjection subgroup left (MonoidAlgebra.single member 1) := by
  apply LinearMap.ext
  intro value
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, subgroupBimoduleProjection_apply]
  conv_lhs => rw [← groupAlgebra_sum_single right]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro member _
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  change left * value * MonoidAlgebra.single member.val (right.coeff member) =
    right.coeff member • (left * value * MonoidAlgebra.single member.val 1)
  have hequal : (MonoidAlgebra.single member.val (right.coeff member) : MonoidAlgebra ring group) =
      right.coeff member • MonoidAlgebra.single member.val 1 := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hequal, mul_smul_comm]

theorem subgroupBimoduleProjection_single_twoSided {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (coefficient : MonoidAlgebra ring group) (member : subgroup) (left right : group) :
    subgroupBimoduleProjection subgroup coefficient (MonoidAlgebra.single member 1) *
      Representation.ofMulAction ring (Equiv.Perm group) group (groupTwoSidedPermutationHom group (left, right)) =
      groupAlgebraTwoSidedOperator coefficient left (member.val⁻¹ * right) := by
  apply LinearMap.ext
  intro value
  rw [Module.End.mul_apply, subgroupBimoduleProjection_apply,
    groupTwoSidedPermutation_representation]
  change (coefficient * (MonoidAlgebra.single left 1 * (value * MonoidAlgebra.single right⁻¹ 1))) *
      MonoidAlgebra.mapDomainRingHom ring subgroup.subtype (MonoidAlgebra.single member 1) =
    coefficient * (MonoidAlgebra.single left 1 * (value * MonoidAlgebra.single (member.val⁻¹ * right)⁻¹ 1))
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [mul_inv_rev, inv_inv]
  calc
    _ = coefficient * (MonoidAlgebra.single left 1 *
        (value * (MonoidAlgebra.single right⁻¹ 1 * MonoidAlgebra.single member.val 1))) := by
          simp only [mul_assoc]
          rfl
    _ = _ := by rw [MonoidAlgebra.single_mul_single, one_mul]

theorem characterSubsetBimodule_twoSided_trace {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (subgroup : Subgroup group) (rightCoefficient : MonoidAlgebra ℂ subgroup)
    (left : group) (right : subgroup) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (subgroupBimoduleProjection subgroup (characterSubsetIdempotent basis support) rightCoefficient *
        Representation.ofMulAction ℂ (Equiv.Perm group) group (groupTwoSidedPermutationHom group (left, right.val))) =
      ∑ label ∈ support, (basis.representation label).character left *
        ∑ member : subgroup, rightCoefficient.coeff member *
          (basis.representation label).character (right.val⁻¹ * member.val) := by
  rw [subgroupBimoduleProjection_expansion, Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, smul_eq_mul, subgroupBimoduleProjection_single_twoSided,
    characterSubsetIdempotent_twoSided_trace, mul_inv_rev, inv_inv]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro member _
  ring

theorem characterSubsetBimodule_local_projection_trace {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (subgroup : Subgroup group) (localBasis : FiniteIrreducibleCharacterBasis subgroup)
    (localSupport : Finset localBasis.index) (left : group) (right : subgroup) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ group)
      (subgroupBimoduleProjection subgroup (characterSubsetIdempotent basis support)
          (characterSubsetIdempotent localBasis localSupport) *
        Representation.ofMulAction ℂ (Equiv.Perm group) group (groupTwoSidedPermutationHom group (left, right.val))) =
      ∑ label ∈ support, (basis.representation label).character left *
        characterSubsetProjection localBasis localSupport
          (fun member : subgroup => (basis.representation label).character member.val) right⁻¹ := by
  rw [characterSubsetBimodule_twoSided_trace]
  apply Finset.sum_congr rfl
  intro label _
  congr 1
  rw [characterSubsetProjection_convolution]
  · rfl
  · intro member conjugator
    change (basis.representation label).representation.character
      (conjugator.val * member.val * conjugator.val⁻¹) = _
    exact Representation.char_conj (basis.representation label).representation member.val conjugator.val

end CFSG.TwoRankLowerBound.Helpers
