module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallTransport
public import CFSG.GH74.KGroups.L27
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.L27

public section

namespace CFSG.ComponentClassification.FooteSmall.L27

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L27

@[expose] def q1 : Equiv.Perm (Fin 8) := List.formPerm [0, 2, 1, 4, 7, 3, 6, 5]

@[expose] def q2 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 2] * List.formPerm [1, 5] * List.formPerm [3, 7] * List.formPerm [4, 6]

@[expose] def Q0list : List (Equiv.Perm (Fin 8)) :=
  search 3 [q1, q2] 64
    ((Array.replicate (8 ^ 3) false).set! (key 3 (1 : Equiv.Perm (Fin 8))) true) [1] [1]

@[expose] def a0 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 5] * List.formPerm [1, 3] * List.formPerm [2, 6] * List.formPerm [4, 7]

@[expose] def b0 : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 3] * List.formPerm [1, 4] * List.formPerm [2, 7] * List.formPerm [5, 6]

end CFSG.ComponentClassification.FooteSmall.L27
