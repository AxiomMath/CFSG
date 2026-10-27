module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Cycle.Basic
public meta import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm
@[expose] def inv6 : List (Perm (Fin 6)) :=
  (allPerms 6).filter fun s => s * s = 1 ∧ s ≠ 1 ∧ sign s = 1

@[expose] def ord3six : List (Perm (Fin 6)) :=
  (allPerms 6).filter fun s => s * s * s = 1 ∧ s ≠ 1

@[expose] def even6 : List (Perm (Fin 6)) :=
  (allPerms 6).filter fun s => sign s = 1

@[expose] def goodW (a1 a2 c : Perm (Fin 6)) : Bool :=
  decide (c * a1 = a1 * c ∧ c ≠ 1 ∧ c ≠ a1 ∧ c ≠ a2 ∧ c ≠ a1 * a2)

@[expose] def okB6 (a1 a2 τ b : Perm (Fin 6)) : Bool :=
  if b * τ = τ * b ∧ b ≠ 1 ∧ b ≠ τ ∧ b ≠ τ⁻¹ then
    goodW a1 a2 (b * a2 * b⁻¹ * a1 * a2 * b) || goodW a1 a2 (b * a1 * b⁻¹ * a1 * b) ||
      goodW a1 a2 (b * a1 * a2 * b⁻¹ * a2 * b)
  else true

@[expose] def okT6 (a1 a2 τ : Perm (Fin 6)) : Bool :=
  if (τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2) ∧
      (τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2) then
    even6.all (okB6 a1 a2 τ)
  else true

@[expose] def okP6 (a1 a2 : Perm (Fin 6)) : Bool :=
  if a1 * a2 = a2 * a1 ∧ a1 ≠ a2 then ord3six.all (okT6 a1 a2) else true

@[expose] def okC6 : Bool := inv6.all fun a1 => inv6.all (okP6 a1)

end CFSG.GH74.GLS.C3.Prop121
