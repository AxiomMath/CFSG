module

public import Mathlib.GroupTheory.Perm.List

public section

namespace CFSG.OddStandard.SmallF3.L33

@[expose] def modelX : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 2, 9, 6, 4, 7, 12, 5] * List.formPerm [1, 8, 3, 11]
    * List.formPerm [13, 18, 24, 20] * List.formPerm [14, 25, 17, 15, 16, 19, 23, 22]

@[expose] def modelY : Equiv.Perm (Fin 26) :=
  List.formPerm [1, 3] * List.formPerm [2, 6] * List.formPerm [5, 7] * List.formPerm [9, 12]
    * List.formPerm [14, 16] * List.formPerm [15, 19] * List.formPerm [18, 20]
    * List.formPerm [22, 25]

@[expose] def modelK : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 17] * List.formPerm [1, 20] * List.formPerm [2, 22] * List.formPerm [3, 18]
    * List.formPerm [4, 23] * List.formPerm [5, 19] * List.formPerm [6, 25]
    * List.formPerm [7, 15] * List.formPerm [8, 13] * List.formPerm [9, 16]
    * List.formPerm [10, 21] * List.formPerm [11, 24] * List.formPerm [12, 14]

@[expose] def modelZ : Equiv.Perm (Fin 26) := modelX ^ 4

@[expose] def modelG1 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 12, 1] * List.formPerm [3, 4, 9] * List.formPerm [5, 7, 6]
    * List.formPerm [8, 10, 11] * List.formPerm [13, 21, 24] * List.formPerm [14, 20, 17]
    * List.formPerm [15, 25, 19] * List.formPerm [16, 18, 23]

@[expose] def modelG2 : Equiv.Perm (Fin 26) :=
  List.formPerm [1, 10, 3] * List.formPerm [2, 8, 6] * List.formPerm [4, 9, 12]
    * List.formPerm [5, 7, 11] * List.formPerm [13, 19, 15] * List.formPerm [14, 16, 17]
    * List.formPerm [18, 20, 21] * List.formPerm [22, 24, 25]

end CFSG.OddStandard.SmallF3.L33
