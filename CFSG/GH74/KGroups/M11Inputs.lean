module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.GH74.KGroups.M11

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
@[expose] def words : List (List ℤ) :=
  [[-1, 2, 1], [-2, 3, 2], [3, 4, -3], [-4, -5], [-4, -6, 4, 5], [4, -5, -3, -4, 5, 3, 3]]

@[expose] def Q : RawSchreierDatum 11 :=
  certificate (by decide) [m11gA, m11gB] words #v[1, 0, 2, 3] (by decide)

@[expose] def m11x0 : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9, 5] * List.formPerm [3, 6, 7] * List.formPerm [4, 10, 8]

@[expose] def ws : List (List Bool × ℕ) :=
  [([false, true], 11), ([false, true, false, true, true, false, true, true, true], 3)]

section Consequences

variable {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11)

include h

end Consequences

end CFSG.GH74.KGroups.M11
