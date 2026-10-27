module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallTransport
public import CFSG.GH74.KGroups.A7
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A7

public section

namespace CFSG.ComponentClassification.FooteSmall.A7

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A7

@[expose] def q1 : Equiv.Perm (Fin 7) := List.formPerm [0, 1] * List.formPerm [2, 3, 5, 4]

@[expose] def q2 : Equiv.Perm (Fin 7) := List.formPerm [0, 1] * List.formPerm [2, 5]

@[expose] def q3 : Equiv.Perm (Fin 7) := List.formPerm [2, 3, 5, 4]

@[expose] def Q0list : List (Equiv.Perm (Fin 7)) :=
  search 6 [q1, q2, q3] 64
    ((Array.replicate (7 ^ 6) false).set! (key 6 (1 : Equiv.Perm (Fin 7))) true) [1] [1]

@[expose] def a0 : Equiv.Perm (Fin 7) := List.formPerm [0, 1] * List.formPerm [2, 5]

@[expose] def b0 : Equiv.Perm (Fin 7) := List.formPerm [2, 4] * List.formPerm [3, 5]

end CFSG.ComponentClassification.FooteSmall.A7
