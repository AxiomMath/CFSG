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
public import CFSG.Assembly.OrderReductions.InvariantSylow

public section

namespace CFSG.OrderReductions.InvariantQuotient

@[expose] def quotientAutomorphism {group : Type*} [Group group]
    (automorphism : MulAut group) (normal : Subgroup group) [normal.Normal]
    (invariant : normal.map automorphism.toMonoidHom = normal) : MulAut (group ⧸ normal) :=
  QuotientGroup.congr normal normal automorphism invariant

theorem quotientAutomorphism_apply {group : Type*} [Group group]
    (automorphism : MulAut group) (normal : Subgroup group) [normal.Normal]
    (invariant : normal.map automorphism.toMonoidHom = normal) (element : group) :
    quotientAutomorphism automorphism normal invariant (QuotientGroup.mk' normal element) =
      QuotientGroup.mk' normal (automorphism element) :=
  QuotientGroup.congr_mk' normal normal automorphism invariant element

theorem quotientAutomorphism_involutive {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (normal : Subgroup group) [normal.Normal]
    (invariant : normal.map automorphism.toMonoidHom = normal) :
    Function.Involutive (quotientAutomorphism automorphism normal invariant) := by
  intro point
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective normal point
  rw [quotientAutomorphism_apply, quotientAutomorphism_apply, involutive]

theorem quotientAutomorphism_mul {group : Type*} [Group group]
    (first second : MulAut group) (normal : Subgroup group) [normal.Normal]
    (first_invariant : normal.map first.toMonoidHom = normal)
    (second_invariant : normal.map second.toMonoidHom = normal)
    (product_invariant : normal.map (first * second : MulAut group).toMonoidHom = normal) :
    quotientAutomorphism (first * second) normal product_invariant =
      quotientAutomorphism first normal first_invariant *
        quotientAutomorphism second normal second_invariant := by
  apply MulEquiv.ext
  intro point
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective normal point
  change quotientAutomorphism (first * second) normal product_invariant
      (QuotientGroup.mk' normal element) =
    quotientAutomorphism first normal first_invariant
      (quotientAutomorphism second normal second_invariant (QuotientGroup.mk' normal element))
  rw [quotientAutomorphism_apply, quotientAutomorphism_apply, quotientAutomorphism_apply]
  rfl

theorem quotientAutomorphism_commutes {group : Type*} [Group group]
    (first second : MulAut group)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (normal : Subgroup group) [normal.Normal]
    (first_invariant : normal.map first.toMonoidHom = normal)
    (second_invariant : normal.map second.toMonoidHom = normal) (point : group ⧸ normal) :
    quotientAutomorphism first normal first_invariant
        (quotientAutomorphism second normal second_invariant point) =
      quotientAutomorphism second normal second_invariant
        (quotientAutomorphism first normal first_invariant point) := by
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective normal point
  rw [quotientAutomorphism_apply, quotientAutomorphism_apply,
    quotientAutomorphism_apply, quotientAutomorphism_apply, commutes]

theorem restrictedAutomorphism_commutes {group : Type*} [Group group]
    (first second : MulAut group)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (subgroup : Subgroup group)
    (first_invariant : subgroup.map first.toMonoidHom = subgroup)
    (second_invariant : subgroup.map second.toMonoidHom = subgroup) (element : subgroup) :
    CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism first subgroup first_invariant
        (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism second subgroup second_invariant element) =
      CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism second subgroup second_invariant
        (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism first subgroup first_invariant element) := by
  apply Subtype.ext
  exact commutes element.val

@[expose] def quotientHomomorphism {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (normal : Subgroup group) [normal.Normal]
    (invariant : ∀ acting : actor, normal.map (action acting).toMonoidHom = normal) :
    actor →* MulAut (group ⧸ normal) where
  toFun acting := quotientAutomorphism (action acting) normal (invariant acting)
  map_one' := by
    ext point
    induction point using QuotientGroup.induction_on with
    | H element =>
        change quotientAutomorphism (action 1) normal (invariant 1) (QuotientGroup.mk' normal element) =
          QuotientGroup.mk' normal element
        rw [quotientAutomorphism_apply, map_one]
        rfl
  map_mul' first second := by
    ext point
    induction point using QuotientGroup.induction_on with
    | H element =>
        change quotientAutomorphism (action (first * second)) normal (invariant (first * second))
          (QuotientGroup.mk' normal element) =
            quotientAutomorphism (action first) normal (invariant first)
              (quotientAutomorphism (action second) normal (invariant second)
                (QuotientGroup.mk' normal element))
        rw [quotientAutomorphism_apply, quotientAutomorphism_apply, quotientAutomorphism_apply,
          map_mul]
        rfl

end CFSG.OrderReductions.InvariantQuotient
