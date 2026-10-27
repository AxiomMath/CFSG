module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallTransport
public import CFSG.GH74.KGroups.A6
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A6

public section

namespace CFSG.ComponentClassification.FooteSmall.A6

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6

@[expose] def q1 : Equiv.Perm (Fin 10) := List.formPerm [0, 3, 9, 6] * List.formPerm [4, 8, 5, 7]

@[expose] def q2 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 5] * List.formPerm [1, 2] * List.formPerm [3, 8] * List.formPerm [4, 9] *
    List.formPerm [6, 7]

@[expose] def q3 : Equiv.Perm (Fin 10) := List.formPerm [0, 8, 3, 5, 9, 7, 6, 4]

@[expose] def q4 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 5, 3, 7, 9, 4, 6, 8] * List.formPerm [1, 2]

@[expose] def Q0list : List (Equiv.Perm (Fin 10)) :=
  search 4 [q1, q2, q3, q4] 64
    ((Array.replicate (10 ^ 4) false).set! (key 4 (1 : Equiv.Perm (Fin 10))) true) [1] [1]

@[expose] def a0 : Equiv.Perm (Fin 10) :=
  List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 8] * List.formPerm [5, 7]

@[expose] def b0 : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 6] * List.formPerm [1, 2] * List.formPerm [3, 9] * List.formPerm [7, 8]

end CFSG.ComponentClassification.FooteSmall.A6
