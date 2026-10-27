module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22Inputs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open scoped commutatorElement

@[expose] def m22E8KL : List (Equiv.Perm (Fin 22)) := enumerationTab m22CentQ1

@[expose] def m22E8UL : List (Equiv.Perm (Fin 22)) := permClosureList m22UGens1 20

@[expose] def m22E8X : Equiv.Perm (Fin 22) := m22KGens1.getD 0 1

@[expose] def m22E8Y : Equiv.Perm (Fin 22) := m22KGens1.getD 1 1

@[expose] def m22E8U0 : Equiv.Perm (Fin 22) := m22UGens1.getD 0 1

@[expose] def m22E8U1 : Equiv.Perm (Fin 22) := m22UGens1.getD 1 1

@[expose] def m22E8U2 : Equiv.Perm (Fin 22) := m22UGens1.getD 2 1

@[expose] def m22E8CommGens : List (Equiv.Perm (Fin 22)) :=
  [⁅m22E8U0, m22E8U1⁆, ⁅m22E8U0, m22E8U2⁆, ⁅m22E8U1, m22E8U2⁆]

@[expose] def m22E8EL : List (Equiv.Perm (Fin 22)) := permClosureList m22E8CommGens 20

@[expose] def m22E8Check : Bool :=
  decide (m22E8UL.length = 64) &&
  decide m22E8UL.Nodup &&
  m22UGens1.all (fun g => decide (g ∈ m22E8UL)) &&
  decide (m22E8U0 ∈ m22E8UL) &&
  decide (m22E8U1 ∈ m22E8UL) &&
  decide (m22E8U2 ∈ m22E8UL) &&
  decide (m22E8X ∈ m22E8KL) &&
  decide (m22E8Y ∈ m22E8KL) &&
  decide (⁅m22E8X, m22E8Y⁆ ∉ m22E8UL) &&
  decide (m22E8EL.length = 8) &&
  decide m22E8EL.Nodup &&
  decide ((1 : Equiv.Perm (Fin 22)) ∈ m22E8EL) &&
  m22E8EL.all (fun x => m22E8EL.all fun y => decide (x * y ∈ m22E8EL)) &&
  m22E8EL.all (fun x => decide (x⁻¹ ∈ m22E8EL)) &&
  m22E8EL.all (fun x => decide (x ^ 2 = 1)) &&
  m22E8EL.all (fun x => m22E8EL.all fun y => decide (x * y = y * x)) &&
  m22E8EL.all (fun x => decide (x ∈ m22E8UL)) &&
  m22E8CommGens.all (fun x => decide (x ∈ m22E8EL)) &&
  m22E8UL.all (fun x => m22E8UL.all fun y => decide (⁅x, y⁆ ∈ m22E8EL))

structure M22E8Facts : Prop where
  ul_length : m22E8UL.length = 64
  ul_nodup : m22E8UL.Nodup
  ugens_mem : ∀ g ∈ m22UGens1, g ∈ m22E8UL
  u0_mem : m22E8U0 ∈ m22E8UL
  u1_mem : m22E8U1 ∈ m22E8UL
  u2_mem : m22E8U2 ∈ m22E8UL
  x_mem : m22E8X ∈ m22E8KL
  y_mem : m22E8Y ∈ m22E8KL
  xy_not_mem : ⁅m22E8X, m22E8Y⁆ ∉ m22E8UL
  el_length : m22E8EL.length = 8
  el_nodup : m22E8EL.Nodup
  el_one : (1 : Equiv.Perm (Fin 22)) ∈ m22E8EL
  el_mul : ∀ x ∈ m22E8EL, ∀ y ∈ m22E8EL, x * y ∈ m22E8EL
  el_inv : ∀ x ∈ m22E8EL, x⁻¹ ∈ m22E8EL
  el_sq : ∀ x ∈ m22E8EL, x ^ 2 = 1
  el_comm : ∀ x ∈ m22E8EL, ∀ y ∈ m22E8EL, x * y = y * x
  el_le_ul : ∀ x ∈ m22E8EL, x ∈ m22E8UL
  commgens_mem : ∀ x ∈ m22E8CommGens, x ∈ m22E8EL
  ul_comm_mem : ∀ x ∈ m22E8UL, ∀ y ∈ m22E8UL, ⁅x, y⁆ ∈ m22E8EL

theorem m22E8Facts_of_check (h : m22E8Check = true) : M22E8Facts := by
  simp only [m22E8Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨h_ul_length, h_ul_nodup, h_ugens_mem, h_u0_mem, h_u1_mem, h_u2_mem,
    h_x_mem, h_y_mem, h_xy_not_mem, h_el_length, h_el_nodup, h_el_one, h_el_mul,
    h_el_inv, h_el_sq, h_el_comm, h_el_le_ul, h_commgens_mem, h_ul_comm_mem⟩ := h
  exact ⟨h_ul_length, h_ul_nodup, h_ugens_mem, h_u0_mem, h_u1_mem, h_u2_mem,
    h_x_mem, h_y_mem, h_xy_not_mem, h_el_length, h_el_nodup, h_el_one, h_el_mul,
    h_el_inv, h_el_sq, h_el_comm, h_el_le_ul, h_commgens_mem, h_ul_comm_mem⟩

end CFSG.ClassicalInvolution
