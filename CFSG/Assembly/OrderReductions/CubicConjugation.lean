module

public import Mathlib
public import CFSG.Mathlib.GroupTheory.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.ClassTwoCubic

public section

namespace CFSG.OrderReductions.CubicConjugation

open CFSG.OrderReductions.ClassTwoCubic

@[expose] def inverseFirstCommutator {group : Type*} [Group group] (first second : group) : group :=
  first⁻¹ * second⁻¹ * first * second

theorem inverseFirstCommutator_swap {group : Type*} [Group group] (first second : group) :
    inverseFirstCommutator second first = (inverseFirstCommutator first second)⁻¹ := by
  dsimp [inverseFirstCommutator]
  group

@[expose] def rightConjugation {group : Type*} [Group group] (normal : Subgroup group) [normal.Normal]
    (conjugator : group) : MulAut normal where
  toFun element := ⟨conjugator⁻¹ * element.val * conjugator,
    Subgroup.Normal.conj_mem' inferInstance element.val element.property conjugator⟩
  invFun element := ⟨conjugator * element.val * conjugator⁻¹,
    Subgroup.Normal.conj_mem inferInstance element.val element.property conjugator⟩
  left_inv element := by
    apply Subtype.ext
    change conjugator * (conjugator⁻¹ * element.val * conjugator) * conjugator⁻¹ = element.val
    group
  right_inv element := by
    apply Subtype.ext
    change conjugator⁻¹ * (conjugator * element.val * conjugator⁻¹) * conjugator = element.val
    group
  map_mul' first second := by
    apply Subtype.ext
    change conjugator⁻¹ * (first.val * second.val) * conjugator =
      (conjugator⁻¹ * first.val * conjugator) * (conjugator⁻¹ * second.val * conjugator)
    group

@[expose] def abelianConjugationAction {group : Type*} [Group group]
    (actors normal : Subgroup group) [IsMulCommutative actors] [normal.Normal] :
    actors →* MulAut normal where
  toFun actor := rightConjugation normal actor.val
  map_one' := by
    ext element
    change (1 : group)⁻¹ * element.val * 1 = element.val
    simp only [inv_one, one_mul, mul_one]
  map_mul' first second := by
    ext element
    change (first.val * second.val)⁻¹ * element.val * (first.val * second.val) =
      first.val⁻¹ * (second.val⁻¹ * element.val * second.val) * first.val
    rw [setLike_mul_comm first.property second.property]
    group

theorem difference_val {group : Type*} [Group group]
    (normal : Subgroup group) [normal.Normal] (conjugator : group) (element : normal) :
    (difference (rightConjugation normal conjugator) element).val =
      inverseFirstCommutator element.val conjugator := by
  dsimp [difference, rightConjugation, inverseFirstCommutator]
  group

theorem internal_commutator_map {group : Type*} [Group group] (subgroup : Subgroup group) :
    (commutator subgroup).map subgroup.subtype = ⁅subgroup, subgroup⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range]

theorem cubic_trivial_conjugation_abelian {group : Type*} [Group group]
    (actors normal : Subgroup group) [IsMulCommutative actors] [normal.Normal]
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (centralizes : actors ≤ Subgroup.centralizer ((⁅normal, normal⁆ : Subgroup group) : Set group))
    (element : normal)
    (cubic : ∀ first second third : actors,
      inverseFirstCommutator
        (inverseFirstCommutator (inverseFirstCommutator element.val first.val) second.val) third.val = 1) :
    IsMulCommutative ↥(Subgroup.closure
      (Set.range fun actor : actors => inverseFirstCommutator element.val actor.val)) := by
  let : CommGroup actors :=
    { (inferInstance : Group actors) with mul_comm := isMulCommutative_iff.mp inferInstance }
  let action := abelianConjugationAction actors normal
  have fixed_commutator : ∀ actor : actors, ∀ value : normal,
      value ∈ commutator normal → action actor value = value := by
    intro actor value value_mem
    have ambient_mem : value.val ∈ ⁅normal, normal⁆ := by
      rw [← internal_commutator_map normal]
      exact Subgroup.mem_map.mpr ⟨value, value_mem, rfl⟩
    have commutes := Subgroup.mem_centralizer_iff.mp (centralizes actor.property) value.val ambient_mem
    apply Subtype.ext
    change actor.val⁻¹ * value.val * actor.val = value.val
    rw [mul_assoc, commutes]
    group
  have cubic_internal : ∀ first second third : actors,
      difference (action third) (difference (action second) (difference (action first) element)) = 1 := by
    intro first second third
    apply Subtype.ext
    change (difference (rightConjugation normal third.val)
      (difference (rightConjugation normal second.val)
        (difference (rightConjugation normal first.val) element))).val = 1
    rw [difference_val, difference_val, difference_val]
    exact cubic first second third
  let internal := Subgroup.closure (Set.range fun actor : actors => difference (action actor) element)
  have : IsMulCommutative internal :=
    cubic_trivial_differences_abelian action central odd_order fixed_commutator element cubic_internal
  apply CFSG.subgroup_isMulCommutative_closure
  rintro left ⟨first, rfl⟩ right ⟨second, rfl⟩
  have commutes := setLike_mul_comm (s := internal)
    (Subgroup.subset_closure (Set.mem_range_self first))
    (Subgroup.subset_closure (Set.mem_range_self second))
  have ambient_commutes := congrArg (fun value : normal => value.val) commutes
  change (difference (rightConjugation normal first.val) element).val *
    (difference (rightConjugation normal second.val) element).val =
    (difference (rightConjugation normal second.val) element).val *
      (difference (rightConjugation normal first.val) element).val at ambient_commutes
  simpa only [difference_val] using ambient_commutes

end CFSG.OrderReductions.CubicConjugation
