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
@[expose] def threeCyc (n : ℕ) : List (Perm (Fin n)) :=
  (allPerms n).filter fun c => c.support.card = 3

@[expose] def okCent (n : ℕ) : Bool :=
  let tc := threeCyc n
  (allPerms n).all fun ρ => decide (ρ = 1) || tc.any fun c => decide (ρ * c ≠ c * ρ)

end CFSG.GH74.GLS.C3.Prop121
