module

public import CFSG.CharacterTheory.TwoRankLowerBound.SubgroupCoefficientProjection

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_subgroup_inclusion_coeff {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring subgroup) (element : subgroup) :
    (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype value).coeff element.val = value.coeff element := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective subgroup.subtype_injective value.coeff element

theorem groupAlgebra_subgroup_inclusion_coeff_zero {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring subgroup) (element : group) (hnot : element ∉ subgroup) :
    (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype value).coeff element = 0 := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨member, hequal⟩
  exact hnot (hequal ▸ member.property)

theorem subgroupCoefficientProjection_inclusion {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring subgroup) :
    subgroupCoefficientProjection subgroup (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype value) = value := by
  ext element
  rw [subgroupCoefficientProjection_coeff, groupAlgebra_subgroup_inclusion_coeff]

theorem subgroupCoefficientProjection_mul_single {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring group) (element : subgroup) :
    subgroupCoefficientProjection subgroup (value * MonoidAlgebra.single element.val 1) =
      subgroupCoefficientProjection subgroup value * MonoidAlgebra.single element 1 := by
  ext member
  rw [subgroupCoefficientProjection_coeff, MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_mul_single_apply, subgroupCoefficientProjection_coeff]
  rfl

theorem subgroupCoefficientProjection_single_mul {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring group) (element : subgroup) :
    subgroupCoefficientProjection subgroup (MonoidAlgebra.single element.val 1 * value) =
      MonoidAlgebra.single element 1 * subgroupCoefficientProjection subgroup value := by
  ext member
  rw [subgroupCoefficientProjection_coeff, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_single_mul_apply, subgroupCoefficientProjection_coeff]
  rfl

theorem subgroupCoefficientProjection_mul_inclusion {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup) :
    subgroupCoefficientProjection subgroup
      (left * MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right) =
      subgroupCoefficientProjection subgroup left * right := by
  have hequal : (subgroupCoefficientProjection subgroup).comp
      ((Algebra.lmul ring (MonoidAlgebra ring group) left).comp
        (MonoidAlgebra.mapDomainAlgHom ring ring subgroup.subtype).toLinearMap) =
      Algebra.lmul ring (MonoidAlgebra ring subgroup) (subgroupCoefficientProjection subgroup left) := by
    apply (MonoidAlgebra.basis subgroup ring).ext
    intro element
    change subgroupCoefficientProjection subgroup
      (left * MonoidAlgebra.mapDomainRingHom ring subgroup.subtype (MonoidAlgebra.single element 1)) = _
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    exact subgroupCoefficientProjection_mul_single subgroup left element
  exact congrArg (fun operator : Module.End ring (MonoidAlgebra ring subgroup) => operator right) hequal

theorem subgroupCoefficientProjection_inclusion_mul {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring subgroup) (right : MonoidAlgebra ring group) :
    subgroupCoefficientProjection subgroup
      (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype left * right) =
      left * subgroupCoefficientProjection subgroup right := by
  have hequal : (subgroupCoefficientProjection subgroup).comp
      ((LinearMap.mulRight ring right).comp
        (MonoidAlgebra.mapDomainAlgHom ring ring subgroup.subtype).toLinearMap) =
      LinearMap.mulRight ring (subgroupCoefficientProjection subgroup right) := by
    apply (MonoidAlgebra.basis subgroup ring).ext
    intro element
    change subgroupCoefficientProjection subgroup
      (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype (MonoidAlgebra.single element 1) * right) = _
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    exact subgroupCoefficientProjection_single_mul subgroup right element
  exact congrArg (fun operator : Module.End ring (MonoidAlgebra ring subgroup) => operator left) hequal

theorem subgroupCoefficientProjection_map_coefficients {ring target group : Type*}
    [CommRing ring] [CommRing target] [Group group] [Fintype group]
    (embedding : ring →+* target) (subgroup : Subgroup group) (value : MonoidAlgebra ring group) :
    subgroupCoefficientProjection subgroup (MonoidAlgebra.mapRingHom group embedding value) =
      MonoidAlgebra.mapRingHom subgroup embedding (subgroupCoefficientProjection subgroup value) := by
  ext element
  simp only [subgroupCoefficientProjection_coeff, MonoidAlgebra.coeff_mapRingHom]

end CFSG.TwoRankLowerBound.Helpers
