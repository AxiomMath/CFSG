module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks
public meta import Mathlib

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L216M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Matrix
@[expose] def pa : Equiv.Perm (Fin 17) :=
  List.formPerm [0, 16] * List.formPerm [2, 9] * List.formPerm [3, 14] * List.formPerm [4, 13]
  * List.formPerm [5, 11] * List.formPerm [6, 7] * List.formPerm [8, 15] * List.formPerm [10, 12]

@[expose] def pb : Equiv.Perm (Fin 17) :=
  List.formPerm [0, 16, 9] * List.formPerm [1, 4, 7] * List.formPerm [2, 6, 12]
  * List.formPerm [5, 15, 11] * List.formPerm [8, 14, 13]

@[expose] def sg : Equiv.Perm (Fin 17) :=
  List.formPerm [2, 4, 3, 5] * List.formPerm [6, 7] * List.formPerm [8, 12, 15, 10]
  * List.formPerm [9, 13, 14, 11]

@[expose] def QP : RawSchreierDatum 17 :=
  certificate (by decide) [pa, pb] [[-1, 2], [3, 3, 3, 2, 3, -1, -3, -3, -2]] #v[0, 1, 2]
    (by decide)

@[expose] def QA : RawSchreierDatum 17 :=
  certificate (by decide) [pa, pb, sg]
    [[-1, 2], [-3, -4, 3, 4], [5, 5, 5, 5, 5, 5, 5, 3, 5, 3], [-5, -6, -5, 4, 6, 3]]
    #v[0, 2, 1, 3] (by decide)

@[expose] def ws : List (List Bool × ℕ) := [([false, true], 15)]

@[expose] def invP : List (Equiv.Perm (Fin 17)) :=
  (elemsT QP).filter fun u => decide (u ≠ 1) && decide (u * u = 1)

end CFSG.GH74.Uniqueness.SU.K.R4.L216M
