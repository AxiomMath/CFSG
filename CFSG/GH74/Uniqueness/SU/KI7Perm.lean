module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.Uniqueness.SU.KI7

open Equiv Equiv.Perm

def pa : Perm (Fin 9) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def pb : Perm (Fin 9) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

def pc : Perm (Fin 9) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

def pt : Perm (Fin 9) := swap 1 2 * swap 2 4 * swap 4 3 * swap 3 6 * swap 6 7 * swap 7 5

def elems : List (Perm (Fin 9)) := [1, pa, pb, pc, pa * pb, pa * pc, pb * pc, pa * (pb * pc)]

theorem sq_elems : ∀ x ∈ elems, x * x = 1 := by
  intro x hx
  simp only [elems, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mul_elems : ∀ x ∈ elems, ∀ y ∈ elems, x * y ∈ elems := by
  intro x hx y hy
  simp only [elems, List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sign_pa : sign pa = 1 := by decide

theorem sign_pb : sign pb = 1 := by decide

theorem sign_pc : sign pc = 1 := by decide

theorem sign_pt : sign pt = 1 := by decide

theorem sign_elems : ∀ x ∈ elems, sign x = 1 := by
  intro x hx
  simp only [elems, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [map_mul, sign_pa, sign_pb, sign_pc]

theorem elems_nodup : elems.Nodup :=
  List.Nodup.of_map (fun σ : Perm (Fin 9) => σ 0) (by decide)

def E : Subgroup (Perm (Fin 9)) where
  carrier := {x | x ∈ elems}
  mul_mem' := fun {x y} hx hy => mul_elems x hx y hy
  one_mem' := by simp [elems]
  inv_mem' := fun {x} hx => by
    have h : x⁻¹ = x := inv_eq_of_mul_eq_one_right (sq_elems x hx)
    rw [h]
    exact hx

theorem mem_E_iff {x : Perm (Fin 9)} : x ∈ E ↔ x = 1 ∨ x = pa ∨ x = pb ∨ x = pc ∨ x = pa * pb ∨
    x = pa * pc ∨ x = pb * pc ∨ x = pa * (pb * pc) := by
  change x ∈ elems ↔ _
  simp [elems]

theorem E_sq {x : Perm (Fin 9)} (hx : x ∈ E) : x * x = 1 := sq_elems x hx

theorem card_E : Nat.card E = 8 := by
  have h : (E : Set (Perm (Fin 9))) = ↑elems.toFinset := by
    ext x
    change x ∈ elems ↔ _
    simp
  calc Nat.card E = Nat.card (E : Set (Perm (Fin 9))) := rfl
    _ = (E : Set (Perm (Fin 9))).ncard := Nat.card_coe_set_eq _
    _ = elems.toFinset.card := by rw [h, Set.ncard_coe_finset]
    _ = elems.length := List.toFinset_card_of_nodup elems_nodup
    _ = 8 := rfl

theorem E_le_alternatingGroup : E ≤ alternatingGroup (Fin 9) := fun x hx =>
  mem_alternatingGroup.mpr (sign_elems x hx)

theorem pa_mem_E : pa ∈ E := mem_E_iff.mpr (Or.inr (Or.inl rfl))

theorem pb_mem_E : pb ∈ E := mem_E_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem pc_mem_E : pc ∈ E := mem_E_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem pt_mem_alternatingGroup : pt ∈ alternatingGroup (Fin 9) :=
  mem_alternatingGroup.mpr sign_pt

theorem pt_pa : pt * pa * pt⁻¹ = pb := by decide

theorem pt_pb : pt * pb * pt⁻¹ = pc := by decide

theorem pt_pc : pt * pc * pt⁻¹ = pa * pb := by decide

theorem pt_pab : pt * (pa * pb) * pt⁻¹ = pb * pc := by decide

theorem pt_pbc : pt * (pb * pc) * pt⁻¹ = pa * (pb * pc) := by decide

theorem pt_pabc : pt * (pa * (pb * pc)) * pt⁻¹ = pa * pc := by decide

theorem pa_ne_one : pa ≠ 1 := by decide

theorem pb_ne_one : pb ≠ 1 := by decide

theorem pc_ne_one : pc ≠ 1 := by decide

theorem pa_mul_pb_ne_one : pa * pb ≠ 1 := by decide

theorem pa_mul_pc_ne_one : pa * pc ≠ 1 := by decide

theorem pb_mul_pc_ne_one : pb * pc ≠ 1 := by decide

theorem pa_mul_pb_mul_pc_ne_one : pa * (pb * pc) ≠ 1 := by decide

end CFSG.GH74.Uniqueness.SU.KI7
