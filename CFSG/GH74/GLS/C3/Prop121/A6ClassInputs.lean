module

public import CFSG.GH74.GLS.C3.Prop121.CentKFin
public meta import CFSG.GH74.GLS.C3.Prop121.CentKFin
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm
@[expose] def okInvConj : Bool :=
  inv6.all fun a => inv6.all fun b => even6.any fun π => decide (π * a * π⁻¹ = b)

end CFSG.GH74.GLS.C3.Prop121
