module

public import Mathlib
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

public section

namespace CFSG.OrderReductions.ClassTwoPairing

attribute [local instance] commutatorElement

local instance centerCommGroup (group : Type*) [Group group] : CommGroup ↥(Subgroup.center group) :=
  { (inferInstance : Group ↥(Subgroup.center group)) with
    mul_comm := fun first second => Subtype.ext (Subgroup.mem_center_iff.mp second.property first.val) }

theorem commutator_central {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first second : group) :
    ⁅first, second⁆ ∈ Subgroup.center group := by
  apply central
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second)

@[expose] def centralCommutator {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first second : group) : Subgroup.center group :=
  ⟨⁅first, second⁆, commutator_central central first second⟩

theorem commutator_mul_left {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first second third : group) :
    ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have conjugate : first * ⁅second, third⁆ * first⁻¹ = ⁅second, third⁆ := by
    rw [Subgroup.mem_center_iff.mp (commutator_central central second third) first,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [conjugate]
  exact Subgroup.mem_center_iff.mp (commutator_central central second third) ⁅first, third⁆ |>.symm

theorem commutator_mul_right {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first second third : group) :
    ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have conjugate : second * ⁅first, third⁆ * second⁻¹ = ⁅first, third⁆ := by
    rw [Subgroup.mem_center_iff.mp (commutator_central central first third) second,
      mul_assoc, mul_inv_cancel, mul_one]
  simpa only [mul_assoc] using congrArg (fun element => ⁅first, second⁆ * element) conjugate

@[expose] def centralCommutatorRightHom {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first : group) : group →* Subgroup.center group where
  toFun := centralCommutator central first
  map_one' := Subtype.ext (commutatorElement_one_right first)
  map_mul' second third := Subtype.ext (commutator_mul_right central first second third)

@[expose] def centralCommutatorHom {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) : group →* group →* Subgroup.center group where
  toFun := centralCommutatorRightHom central
  map_one' := by
    ext element
    change ⁅(1 : group), element⁆ = 1
    exact commutatorElement_one_left element
  map_mul' first second := by
    ext element
    change ⁅first * second, element⁆ = ⁅first, element⁆ * ⁅second, element⁆
    exact commutator_mul_left central first second element

@[expose] noncomputable def commutatorPairing {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) :
    Abelianization group →* Abelianization group →* Subgroup.center group :=
  Abelianization.lift
    { toFun := fun element => Abelianization.lift (centralCommutatorRightHom central element)
      map_one' := by
        apply Abelianization.hom_ext
        ext element
        rw [MonoidHom.comp_apply, Abelianization.lift_apply_of]
        change ⁅(1 : group), element⁆ = 1
        exact commutatorElement_one_left element
      map_mul' first second := by
        apply Abelianization.hom_ext
        ext element
        simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, Abelianization.lift_apply_of]
        change ⁅first * second, element⁆ = ⁅first, element⁆ * ⁅second, element⁆
        exact commutator_mul_left central first second element }

theorem commutatorPairing_of {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (first second : group) :
    commutatorPairing central (Abelianization.of first) (Abelianization.of second) = centralCommutator central first second := by
  unfold commutatorPairing
  rw [Abelianization.lift_apply_of]
  change Abelianization.lift (centralCommutatorRightHom central first) (Abelianization.of second) = _
  rw [Abelianization.lift_apply_of]
  rfl

theorem abelianization_surjective {group : Type*} [Group group] :
    Function.Surjective (Abelianization.of (G := group)) :=
  QuotientGroup.mk'_surjective (commutator group)

theorem commutatorPairing_alternating {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (element : Abelianization group) :
    commutatorPairing central element element = 1 := by
  obtain ⟨original, equal⟩ := abelianization_surjective element
  rw [← equal, commutatorPairing_of]
  exact Subtype.ext (commutatorElement_self original)

theorem commutatorPairing_invariant {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (automorphism : MulAut group)
    (fixed_commutator : ∀ element : group, element ∈ commutator group → automorphism element = element)
    (first second : Abelianization group) :
    commutatorPairing central (Abelianization.map automorphism.toMonoidHom first)
      (Abelianization.map automorphism.toMonoidHom second) = commutatorPairing central first second := by
  obtain ⟨original_first, first_eq⟩ := abelianization_surjective first
  obtain ⟨original_second, second_eq⟩ := abelianization_surjective second
  rw [← first_eq, ← second_eq, Abelianization.map_of, Abelianization.map_of,
    commutatorPairing_of, commutatorPairing_of]
  apply Subtype.ext
  change ⁅automorphism original_first, automorphism original_second⁆ = ⁅original_first, original_second⁆
  rw [← map_commutatorElement]
  apply fixed_commutator
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

@[expose] noncomputable def additiveCommutatorPairing {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) :
    Additive (Abelianization group) →+ Additive (Abelianization group) →+ Additive (Subgroup.center group) where
  toFun element := MonoidHom.toAdditive (commutatorPairing central (Additive.toMul element))
  map_zero' := by
    apply AddMonoidHom.ext
    intro element
    change commutatorPairing central 1 (Additive.toMul element) = 1
    rw [map_one]
    rfl
  map_add' first second := by
    apply AddMonoidHom.ext
    intro element
    change commutatorPairing central (Additive.toMul first * Additive.toMul second) (Additive.toMul element) =
      commutatorPairing central (Additive.toMul first) (Additive.toMul element) *
        commutatorPairing central (Additive.toMul second) (Additive.toMul element)
    rw [map_mul, MonoidHom.mul_apply]

theorem additiveCommutatorPairing_alternating {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (element : Additive (Abelianization group)) :
    additiveCommutatorPairing central element element = 0 :=
  commutatorPairing_alternating central (Additive.toMul element)

@[expose] def abelianizationAutomorphism {group : Type*} [Group group] (automorphism : MulAut group) :
    MulAut (Abelianization group) where
  toFun := Abelianization.map automorphism.toMonoidHom
  invFun := Abelianization.map automorphism.symm.toMonoidHom
  left_inv element := by
    obtain ⟨original, equal⟩ := abelianization_surjective element
    rw [← equal, Abelianization.map_of, Abelianization.map_of]
    change Abelianization.of (automorphism.symm (automorphism original)) = Abelianization.of original
    rw [automorphism.symm_apply_apply]
  right_inv element := by
    obtain ⟨original, equal⟩ := abelianization_surjective element
    rw [← equal, Abelianization.map_of, Abelianization.map_of]
    change Abelianization.of (automorphism (automorphism.symm original)) = Abelianization.of original
    rw [automorphism.apply_symm_apply]
  map_mul' := map_mul _

theorem additiveCommutatorPairing_invariant {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (automorphism : MulAut group)
    (fixed_commutator : ∀ element : group, element ∈ commutator group → automorphism element = element)
    (first second : Additive (Abelianization group)) :
    additiveCommutatorPairing central ((abelianizationAutomorphism automorphism).toAdditive first)
      ((abelianizationAutomorphism automorphism).toAdditive second) = additiveCommutatorPairing central first second :=
  commutatorPairing_invariant central automorphism fixed_commutator (Additive.toMul first) (Additive.toMul second)

end CFSG.OrderReductions.ClassTwoPairing
