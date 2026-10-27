module

public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public meta import CFSG.GH74.GLS.C3.Prop121.L122Fin
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
@[expose] def ok6c : Bool :=
  inv7.all fun a => inv7.all fun b =>
    if a * b = b * a ∧ a ≠ b ∧ a 0 = 0 ∧ b 0 = 0 then
      if ord3.any (fun ρ => decide (ρ * a = a * ρ ∧ ρ * b = b * ρ)) then
        ord3.all fun τ =>
          if (τ * a * τ⁻¹ = b ∨ τ * a * τ⁻¹ = a * b) ∧
              (τ * b * τ⁻¹ = a ∨ τ * b * τ⁻¹ = b ∨ τ * b * τ⁻¹ = a * b) ∧ τ 0 = 0 then
            decide (τ.support.card = 3)
          else true
      else true
    else true

end CFSG.GH74.GLS.C3.Prop121
