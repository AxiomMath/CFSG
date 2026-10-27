module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
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
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm
@[expose] def inv7 : List (Perm (Fin 7)) :=
  (allPerms 7).filter fun s => s * s = 1 ∧ s ≠ 1 ∧ sign s = 1

@[expose] def ord3 : List (Perm (Fin 7)) :=
  (allPerms 7).filter fun s => s * s * s = 1 ∧ s ≠ 1

@[expose] def inV (a b s : Perm (Fin 7)) : Bool := decide (s = 1 ∨ s = a ∨ s = b ∨ s = a * b)

@[expose] def ok122 : Bool :=
  inv7.all fun a => inv7.all fun b =>
    if a * b = b * a ∧ a ≠ b then
      if ord3.any (fun ρ => decide (ρ * a = a * ρ ∧ ρ * b = b * ρ)) then
        ord3.all fun σ =>
          if (σ * a * σ⁻¹ = b ∨ σ * a * σ⁻¹ = a * b) ∧
              (σ * b * σ⁻¹ = a ∨ σ * b * σ⁻¹ = b ∨ σ * b * σ⁻¹ = a * b) then
            if (List.finRange 7).all (fun i => (List.finRange 7).all fun j =>
                decide (i = j) || !(decide (swap i j * a = a * swap i j ∧ swap i j * b = b * swap i j))
                  || inV a b (σ * swap i j * σ⁻¹ * (swap i j)⁻¹)) then
              decide (σ.support.card = 3)
            else true
          else true
      else true
    else true

end CFSG.GH74.GLS.C3.Prop121
