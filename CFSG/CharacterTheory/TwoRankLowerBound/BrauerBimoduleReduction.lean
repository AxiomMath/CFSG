module

public import CFSG.CharacterTheory.TwoRankLowerBound.SubgroupProjectionMultipliers
public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationFixedBasis

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def subgroupBimoduleProjection {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup) :
    Module.End ring (MonoidAlgebra ring group) :=
  (Algebra.lmul ring (MonoidAlgebra ring group) left).comp
    (LinearMap.mulRight ring (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right))

theorem subgroupBimoduleProjection_apply {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (value : MonoidAlgebra ring group) :
    subgroupBimoduleProjection subgroup left right value =
      left * value * MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right := by
  exact (mul_assoc _ _ _).symm

theorem subgroupBimoduleProjection_idempotent {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (hleft : IsIdempotentElem left) (hright : IsIdempotentElem right) :
    IsIdempotentElem (subgroupBimoduleProjection subgroup left right) := by
  apply isIdempotentElem_iff.mpr
  apply LinearMap.ext
  intro value
  simp only [Module.End.mul_apply, subgroupBimoduleProjection_apply]
  have hincluded : MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right *
      MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right =
      MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right := by
    rw [← map_mul, hright.eq]
  calc
    _ = (left * left) * value * (MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right *
        MonoidAlgebra.mapDomainRingHom ring subgroup.subtype right) := by simp only [mul_assoc]
    _ = _ := by rw [hleft.eq, hincluded]

theorem subgroupBimoduleProjection_restrict_basis {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup) (element : subgroup) :
    subgroupCoefficientProjection subgroup
      (subgroupBimoduleProjection subgroup left right (MonoidAlgebra.single element.val 1)) =
      subgroupCoefficientProjection subgroup left * MonoidAlgebra.single element 1 * right := by
  rw [subgroupBimoduleProjection_apply, subgroupCoefficientProjection_mul_inclusion,
    subgroupCoefficientProjection_mul_single]

theorem subgroupBimoduleProjection_residue_coeff_zero {ring residue group : Type*}
    [CommRing ring] [CommRing residue] [Group group] [Fintype group]
    (embedding : ring →+* residue) (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group) (right : MonoidAlgebra ring subgroup)
    (hright : ∀ element : subgroup, Commute right (MonoidAlgebra.single element 1))
    (hzero : MonoidAlgebra.mapRingHom subgroup embedding
      (subgroupCoefficientProjection subgroup left * right) = 0) (row column : subgroup) :
    embedding ((subgroupBimoduleProjection subgroup left right
      (MonoidAlgebra.single column.val 1)).coeff row.val) = 0 := by
  have hequal := congrArg (fun value : MonoidAlgebra ring subgroup => value.coeff row)
    (subgroupBimoduleProjection_restrict_basis subgroup left right column)
  rw [subgroupCoefficientProjection_coeff] at hequal
  rw [hequal, mul_assoc, (hright column).eq.symm, ← mul_assoc]
  change (MonoidAlgebra.mapRingHom subgroup embedding
    ((subgroupCoefficientProjection subgroup left * right) * MonoidAlgebra.single column 1)).coeff row = 0
  rw [map_mul, hzero, zero_mul, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

@[expose, instance_reducible] def subgroupConjugationAction {group : Type*} [Group group] (subgroup : Subgroup group) :
    MulAction subgroup group := MulAction.compHom group (MulAut.conj.comp subgroup.subtype)

theorem conjugation_fixedPoints_iff_centralizer {group : Type*} [Group group] (subgroup : Subgroup group) :
    letI : MulAction subgroup group := subgroupConjugationAction subgroup
    ∀ element : group, element ∈ MulAction.fixedPoints subgroup group ↔
      element ∈ Subgroup.centralizer (subgroup : Set group) := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  intro element
  rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
  constructor
  · intro hfixed member hmember
    have hequal := hfixed (⟨member, hmember⟩ : subgroup)
    change member * element * member⁻¹ = element at hequal
    calc
      _ = (member * element * member⁻¹) * member := by group
      _ = _ := by rw [hequal]
  · intro hcommute member
    change member.val * element * member.val⁻¹ = element
    rw [hcommute member.val member.property]
    group

theorem brauerBimodule_zero_fixedBasis_reduction {ring residue group : Type*}
    [CommRing ring] [CommRing residue] [Group group] [Fintype group]
    (embedding : ring →+* residue) (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (subgroup : Set group)))
    (hright : ∀ element : Subgroup.centralizer (subgroup : Set group),
      Commute right (MonoidAlgebra.single element 1))
    (hzero : MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) left * right) = 0) :
    letI : MulAction subgroup group := subgroupConjugationAction subgroup
    permutationFixedBasisReduction (group := subgroup) embedding
      (subgroupBimoduleProjection (Subgroup.centralizer (subgroup : Set group)) left right) = 0 := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  apply (MonoidAlgebra.basis (MulAction.fixedPoints subgroup group) residue).ext
  intro column
  ext row
  rw [MonoidAlgebra.basis_apply, permutationFixedBasisReduction_coeff, LinearMap.zero_apply,
    MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact subgroupBimoduleProjection_residue_coeff_zero embedding _ left right hright hzero
    ⟨row.val, (conjugation_fixedPoints_iff_centralizer subgroup row.val).mp row.property⟩
    ⟨column.val, (conjugation_fixedPoints_iff_centralizer subgroup column.val).mp column.property⟩

theorem brauerBimodule_fixedBasis_coeff {ring residue group : Type*}
    [CommRing ring] [CommRing residue] [Group group] [Fintype group]
    (embedding : ring →+* residue) (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (subgroup : Set group))) :
    letI : MulAction subgroup group := subgroupConjugationAction subgroup
    ∀ row column : MulAction.fixedPoints subgroup group,
      ((permutationFixedBasisReduction (group := subgroup) embedding
        (subgroupBimoduleProjection (Subgroup.centralizer (subgroup : Set group)) left right))
          (MonoidAlgebra.single column 1)).coeff row =
        (MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding
          (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) left) *
            MonoidAlgebra.single
              (⟨column.val, (conjugation_fixedPoints_iff_centralizer subgroup column.val).mp column.property⟩ :
                Subgroup.centralizer (subgroup : Set group)) 1 *
            MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding right).coeff
              ⟨row.val, (conjugation_fixedPoints_iff_centralizer subgroup row.val).mp row.property⟩ := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  intro row column
  rw [permutationFixedBasisReduction_coeff]
  let centralRow : Subgroup.centralizer (subgroup : Set group) :=
    ⟨row.val, (conjugation_fixedPoints_iff_centralizer subgroup row.val).mp row.property⟩
  let centralColumn : Subgroup.centralizer (subgroup : Set group) :=
    ⟨column.val, (conjugation_fixedPoints_iff_centralizer subgroup column.val).mp column.property⟩
  have hequal := congrArg (fun value : MonoidAlgebra ring (Subgroup.centralizer (subgroup : Set group)) =>
    value.coeff centralRow) (subgroupBimoduleProjection_restrict_basis
      (Subgroup.centralizer (subgroup : Set group)) left right centralColumn)
  rw [subgroupCoefficientProjection_coeff] at hequal
  rw [hequal]
  change (MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) embedding
    (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) left *
      MonoidAlgebra.single centralColumn 1 * right)).coeff centralRow = _
  rw [map_mul, map_mul, MonoidAlgebra.mapRingHom_single, map_one]

theorem subgroupConjugation_representation_eq_twoSided {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group) (element : subgroup) :
    letI : MulAction subgroup group := subgroupConjugationAction subgroup
    Representation.ofMulAction ring subgroup group element =
      (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single element.val 1)).comp
        (LinearMap.mulRight ring (MonoidAlgebra.single element.val⁻¹ 1)) := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  apply LinearMap.ext
  intro value
  ext member
  change ((Representation.ofMulAction ring subgroup group element) value).coeff member =
    (MonoidAlgebra.single element.val 1 * (value * MonoidAlgebra.single element.val⁻¹ 1)).coeff member
  rw [Representation.coeff_ofMulAction, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply]
  simp only [one_mul, mul_one, inv_inv]
  congr 1
  change element.val⁻¹ * member * (element.val⁻¹)⁻¹ = element.val⁻¹ * member * element.val
  rw [inv_inv]

theorem subgroup_centralizer_inclusion_commute_single {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (subgroup : Set group))) (element : subgroup) :
    Commute (MonoidAlgebra.mapDomainRingHom ring (Subgroup.centralizer (subgroup : Set group)).subtype right)
      (MonoidAlgebra.single element.val 1) := by
  have hequal : (Algebra.lmul ring (MonoidAlgebra ring group) (MonoidAlgebra.single element.val 1)).comp
      (MonoidAlgebra.mapDomainAlgHom ring ring
        (Subgroup.centralizer (subgroup : Set group)).subtype).toLinearMap =
      (LinearMap.mulRight ring (MonoidAlgebra.single element.val 1)).comp
        (MonoidAlgebra.mapDomainAlgHom ring ring
          (Subgroup.centralizer (subgroup : Set group)).subtype).toLinearMap := by
    apply (MonoidAlgebra.basis (Subgroup.centralizer (subgroup : Set group)) ring).ext
    intro member
    change MonoidAlgebra.single element.val 1 *
      MonoidAlgebra.mapDomainRingHom ring (Subgroup.centralizer (subgroup : Set group)).subtype
        (MonoidAlgebra.single member 1) =
      MonoidAlgebra.mapDomainRingHom ring (Subgroup.centralizer (subgroup : Set group)).subtype
        (MonoidAlgebra.single member 1) * MonoidAlgebra.single element.val 1
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    simp only [MonoidAlgebra.single_mul_single, one_mul]
    exact congrArg (fun value : group => (MonoidAlgebra.single value 1 : MonoidAlgebra ring group))
      (Subgroup.mem_centralizer_iff.mp member.property element.val element.property)
  exact (congrArg (fun operator => operator right) hequal).symm

theorem brauerBimoduleProjection_equivariant {ring group : Type*}
    [CommRing ring] [Group group] (subgroup : Subgroup group)
    (left : MonoidAlgebra ring group)
    (right : MonoidAlgebra ring (Subgroup.centralizer (subgroup : Set group)))
    (hleft : ∀ element : group, Commute left (MonoidAlgebra.single element 1)) :
    letI : MulAction subgroup group := subgroupConjugationAction subgroup
    permutationMapEquivariant (group := subgroup)
      (subgroupBimoduleProjection (Subgroup.centralizer (subgroup : Set group)) left right) := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  intro element
  rw [subgroupConjugation_representation_eq_twoSided]
  apply LinearMap.ext
  intro value
  let included := MonoidAlgebra.mapDomainRingHom ring (Subgroup.centralizer (subgroup : Set group)).subtype right
  have hleftCommute := hleft element.val
  have hrightCommute : Commute included (MonoidAlgebra.single element.val⁻¹ 1) := by
    exact subgroup_centralizer_inclusion_commute_single subgroup right element⁻¹
  simp only [LinearMap.comp_apply, subgroupBimoduleProjection_apply]
  change left * (MonoidAlgebra.single element.val 1 * (value * MonoidAlgebra.single element.val⁻¹ 1)) * included =
    MonoidAlgebra.single element.val 1 * ((left * value * included) * MonoidAlgebra.single element.val⁻¹ 1)
  calc
    _ = (left * MonoidAlgebra.single element.val 1) * value *
        (MonoidAlgebra.single element.val⁻¹ 1 * included) := by simp only [mul_assoc]
    _ = (MonoidAlgebra.single element.val 1 * left) * value *
        (included * MonoidAlgebra.single element.val⁻¹ 1) := by rw [hleftCommute.eq, hrightCommute.eq]
    _ = _ := by simp only [mul_assoc]

end CFSG.TwoRankLowerBound.Helpers
