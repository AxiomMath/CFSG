module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs
public import Mathlib.GroupTheory.Perm.Centralizer
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS
@[expose] def okOdd (n : ℕ) : Bool :=
  let ps := allPerms n
  ps.all fun σ => !(decide (σ * σ * σ = 1 ∧ σ ≠ 1)) ||
    ps.any fun ρ => decide (ρ * ρ = 1 ∧ sign ρ = -1 ∧ ρ * σ = σ * ρ)

end CFSG.GH74.GLS.C3.Prop121
