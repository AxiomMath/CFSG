module

public import CFSG.CharacterTheory.TwoRankLowerBound.PGroupInvariantSum
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def subgroupCoefficientProjection {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group) :
    MonoidAlgebra ring group →ₗ[ring] MonoidAlgebra ring subgroup where
  toFun := fun value => ∑ element : subgroup, MonoidAlgebra.single element (value.coeff element.val)
  map_add' := by
    intro left right
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.single_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    simp only [MonoidAlgebra.coeff_smul_apply, ← MonoidAlgebra.smul_single, Finset.smul_sum,
      RingHom.id_apply]

theorem subgroupCoefficientProjection_coeff {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group)
    (value : MonoidAlgebra ring group) (element : subgroup) :
    (subgroupCoefficientProjection subgroup value).coeff element = value.coeff element.val := by
  simp only [subgroupCoefficientProjection, LinearMap.coe_mk, AddHom.coe_mk, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem subgroupCoefficientProjection_one {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group] (subgroup : Subgroup group) :
    subgroupCoefficientProjection subgroup (1 : MonoidAlgebra ring group) = 1 := by
  ext element
  rw [subgroupCoefficientProjection_coeff]
  have hequal : (1 : group) = element.val ↔ (1 : subgroup) = element :=
    ⟨fun hequal => Subtype.ext hequal, fun hequal => congrArg Subtype.val hequal⟩
  simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply, hequal]

theorem groupAlgebra_coeff_mul_fintype {ring group : Type*}
    [Semiring ring] [Group group] [Fintype group] (left right : MonoidAlgebra ring group) (element : group) :
    (left * right).coeff element = ∑ member : group, left.coeff member * right.coeff (member⁻¹ * element) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

@[expose] def subgroupConjugationInvariant {ring group : Type*} [CommRing ring] [Group group]
    (subgroup : Subgroup group) (value : MonoidAlgebra ring group) : Prop :=
  ∀ (conjugator : subgroup) (element : group),
    value.coeff (conjugator.val * element * conjugator.val⁻¹) = value.coeff element

theorem prime_centralizer_coefficientProjection_mul {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group]
    (prime : ℕ) [Fact prime.Prime] [CharP ring prime] (subgroup : Subgroup group)
    (hgroup : IsPGroup prime subgroup) (left right : MonoidAlgebra ring group)
    (hleft : subgroupConjugationInvariant subgroup left)
    (hright : subgroupConjugationInvariant subgroup right) :
    subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) (left * right) =
      subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) left *
        subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) right := by
  let : MulAction subgroup group := MulAction.compHom group (MulAut.conj.comp subgroup.subtype)
  have haction : ∀ (conjugator : subgroup) (element : group),
      conjugator • element = conjugator.val * element * conjugator.val⁻¹ := fun _ _ => rfl
  have hfixed : ∀ element : group, element ∈ MulAction.fixedPoints subgroup group ↔
      element ∈ Subgroup.centralizer (subgroup : Set group) := by
    intro element
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hfix member hmember
      have hequal := hfix (⟨member, hmember⟩ : subgroup)
      rw [haction] at hequal
      calc
        _ = (member * element * member⁻¹) * member := by group
        _ = _ := by rw [hequal]
    · intro hcommute member
      rw [haction, hcommute member.val member.property]
      group
  ext element
  rw [subgroupCoefficientProjection_coeff, groupAlgebra_coeff_mul_fintype,
    groupAlgebra_coeff_mul_fintype]
  simp only [subgroupCoefficientProjection_coeff, Subgroup.coe_mul, Subgroup.coe_inv]
  have hinvariant : ∀ (conjugator : subgroup) (member : group),
      left.coeff (conjugator • member) * right.coeff ((conjugator • member)⁻¹ * element.val) =
        left.coeff member * right.coeff (member⁻¹ * element.val) := by
    intro conjugator member
    rw [haction, hleft]
    have hcommute := Subgroup.mem_centralizer_iff.mp element.property conjugator.val conjugator.property
    have hequal : (conjugator.val * member * conjugator.val⁻¹)⁻¹ * element.val =
        conjugator.val * (member⁻¹ * element.val) * conjugator.val⁻¹ := by
      calc
        _ = conjugator.val * member⁻¹ * (conjugator.val⁻¹ * element.val) := by group
        _ = conjugator.val * member⁻¹ * (element.val * conjugator.val⁻¹) := by
          rw [(show Commute conjugator.val element.val from hcommute).inv_left.eq]
        _ = _ := by group
    rw [hequal, hright]
  rw [p_group_invariant_sum_fixedPoints prime hgroup _ hinvariant]
  simp only [hfixed]
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  intro member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end CFSG.TwoRankLowerBound.Helpers
