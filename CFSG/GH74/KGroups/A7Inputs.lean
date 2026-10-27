module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.GH74.KGroups.A7

open CFSG.Certificates CFSG.Sporadic.Schreier
@[expose] def pa : Equiv.Perm (Fin 7) :=
  List.formPerm [3, 4] * List.formPerm [5, 6]

@[expose] def pb : Equiv.Perm (Fin 7) :=
  List.formPerm [0, 1, 2, 3, 5]

@[expose] def sg0 : Equiv.Perm (Fin 7) :=
  List.formPerm [0, 2, 5, 4] * List.formPerm [1, 6, 3]

@[expose] def QP : RawSchreierDatum 7 :=
  certificate (by decide) [pa, pb] [[-1, 2, 1], [3, 2, -3, 1], [-3, -3, 4, 3], [-5, -4, -4, 5, -4]] #v[3, 0, 1, 2, 4] (by decide)

@[expose] def QA : RawSchreierDatum 7 :=
  certificate (by decide) [pa, pb, sg0] [[-1, 2, 1], [4, 3, 4, 1], [-4, -4, -5, 4], [-5, -6, -4, 2, 5, 1], [-6, -6, 7, 6], [-7, -8]]
    #v[3, 0, 1, 2, 5, 4] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 7), ([false, true, false, true, true], 6)]

end CFSG.GH74.KGroups.A7
