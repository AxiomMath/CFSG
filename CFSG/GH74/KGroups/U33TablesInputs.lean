module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.U33
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.U33

public section

namespace CFSG.GH74.KGroups.U33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint
@[expose] def sy0 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 4] * List.formPerm [2, 5] * List.formPerm [3, 6] * List.formPerm [10, 23] * List.formPerm [11, 24] * List.formPerm [12, 22] * List.formPerm [13, 20] * List.formPerm [14, 21] * List.formPerm [15, 19] * List.formPerm [16, 26] * List.formPerm [17, 27] * List.formPerm [18, 25]

@[expose] def sy1 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 7] * List.formPerm [1, 4] * List.formPerm [2, 19] * List.formPerm [3, 10] * List.formPerm [5, 15] * List.formPerm [6, 23] * List.formPerm [8, 9] * List.formPerm [12, 18] * List.formPerm [13, 16] * List.formPerm [17, 27] * List.formPerm [20, 26] * List.formPerm [22, 25]

@[expose] def sy2 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 1, 7, 4] * List.formPerm [2, 23, 19, 6] * List.formPerm [3, 15, 10, 5] * List.formPerm [8, 17, 9, 27] * List.formPerm [11, 21] * List.formPerm [12, 22, 18, 25] * List.formPerm [13, 26, 16, 20] * List.formPerm [14, 24]

@[expose] def sy3 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 9, 7, 8] * List.formPerm [1, 27, 4, 17] * List.formPerm [2, 23, 19, 6] * List.formPerm [3, 5, 10, 15] * List.formPerm [12, 26, 18, 20] * List.formPerm [13, 22, 16, 25]

@[expose] def sy4 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 23, 8, 2, 7, 6, 9, 19] * List.formPerm [1, 15, 17, 10, 4, 5, 27, 3] * List.formPerm [12, 16, 20, 22, 18, 13, 26, 25] * List.formPerm [21, 24]

@[expose] def s0 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 7] * List.formPerm [1, 4] * List.formPerm [2, 19] * List.formPerm [3, 10] * List.formPerm [5, 15] * List.formPerm [6, 23] * List.formPerm [8, 9] * List.formPerm [12, 18] * List.formPerm [13, 16] * List.formPerm [17, 27] * List.formPerm [20, 26] * List.formPerm [22, 25]

@[expose] def t0 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 18] * List.formPerm [1, 11] * List.formPerm [2, 7] * List.formPerm [5, 9] * List.formPerm [6, 13] * List.formPerm [8, 25] * List.formPerm [10, 14] * List.formPerm [12, 19] * List.formPerm [15, 22] * List.formPerm [16, 17] * List.formPerm [21, 26] * List.formPerm [23, 27]

@[expose] def QS : RawSchreierDatum 28 :=
  certificate (by decide) [sy0, sy1, sy2, sy3, sy4] [[-1, 2]]
    #v[1, 0] (by decide)

end CFSG.GH74.KGroups.U33
