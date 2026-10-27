
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.Data.Fintype.Perm
public import CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem mem_evenC5 {s : Perm (Fin 6)} :
    s ∈ evenC5 ↔ s * s = 1 ∧ sign s = 1 ∧ s * cEnd5 * s⁻¹ = cEnd5⁻¹ := by
  simp [evenC5]

theorem mem_a4C5 {s : Perm (Fin 6)} :
    s ∈ a4C5 ↔ s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd5 * s) ^ 3 = 1 := by
  simp [a4C5]

theorem mem_oddC5 {s : Perm (Fin 6)} :
    s ∈ oddC5 ↔ s * s = 1 ∧ sign s = -1 ∧ s * cEnd5 * s⁻¹ = cEnd5⁻¹ := by
  simp [oddC5]

instance (E1 E2 : Finset (Perm (Fin 6))) (s1 : Perm (Fin 6)) : Decidable (searchB5 E1 E2 s1) := by
  unfold searchB5; infer_instance

instance (A O E : Finset (Perm (Fin 6))) : Decidable (searchAll5 A O E) := by
  unfold searchAll5; infer_instance

theorem mem_evenC6 {s : Perm (Fin 7)} :
    s ∈ evenC6 ↔ s * s = 1 ∧ sign s = 1 ∧ s * cEnd6 * s⁻¹ = cEnd6⁻¹ := by
  simp [evenC6]

theorem mem_a4C6 {s : Perm (Fin 7)} :
    s ∈ a4C6 ↔ s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd6 * s) ^ 3 = 1 := by
  simp [a4C6]

theorem mem_oddC6 {s : Perm (Fin 7)} :
    s ∈ oddC6 ↔ s * s = 1 ∧ sign s = -1 ∧ s * cEnd6 * s⁻¹ = cEnd6⁻¹ := by
  simp [oddC6]

instance (E1 E2 : Finset (Perm (Fin 7))) (s1 : Perm (Fin 7)) : Decidable (searchB6 E1 E2 s1) := by
  unfold searchB6; infer_instance

instance (A O E : Finset (Perm (Fin 7))) : Decidable (searchAll6 A O E) := by
  unfold searchAll6; infer_instance

end CFSG.GH74.GLS.C3.Prop121
