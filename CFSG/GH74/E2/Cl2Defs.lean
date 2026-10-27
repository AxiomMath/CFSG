module

public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def FourGen (Q : Type*) [Group Q] : Prop :=
  ∀ H : Subgroup Q, ∃ s : Finset Q, s.card ≤ 4 ∧ Subgroup.closure (s : Set Q) = H

variable {Q : Type*} [Group Q]

@[expose] def fixSub (a : MulAut Q) : Subgroup Q where
  carrier := {x | a x = x}
  mul_mem' := fun {x y} hx hy => by
    change a x = x at hx
    change a y = y at hy
    change a (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one a
  inv_mem' := fun {x} hx => by
    change a x = x at hx
    change a x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_fixSub (a : MulAut Q) (x : Q) : x ∈ fixSub a ↔ a x = x := Iff.rfl

@[expose] def eps (g : MulAut Q) (x : Q) : Q := x * g x * g (g x)

@[expose] def sqsub (A : Subgroup Q) : Subgroup Q := Subgroup.closure {w | ∃ u ∈ A, w = u * u}

structure BPair (Q : Type*) [Group Q] (a b : MulAut Q) : Prop where
  a_cube : a ^ 3 = 1
  b_cube : b ^ 3 = 1
  comm : a * b = b * a
  sup_top : (fixSub a ⊔ frattini Q) ⊔ (fixSub b ⊔ frattini Q) = ⊤
  inf_le : (fixSub a ⊔ frattini Q) ⊓ (fixSub b ⊔ frattini Q) ≤ frattini Q
  a_ne : fixSub a ⊔ frattini Q ≠ ⊤
  b_ne : fixSub b ⊔ frattini Q ≠ ⊤

end CFSG.GH74.E2
