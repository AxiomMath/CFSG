module

public import CFSG.Sporadic.Schreier.M11Data

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m11Invs : List (Equiv.Perm (Fin 11)) := m11Elements.filter (orderIs · 2)

@[expose] def m11Word (x y : Equiv.Perm (Fin 11)) : Equiv.Perm (Fin 11) :=
  x * y * (x * (y * y)) * (x * (y * (y * y)))

@[expose] def m11ConjsA : List (Equiv.Perm (Fin 11)) :=
  m11Elements.map fun h => h * m11gA * h⁻¹

@[expose] def m11G : Fin 3 → Equiv.Perm (Fin 11)
  | 0 => List.formPerm [0, 10] * List.formPerm [3, 9] * List.formPerm [4, 8] * List.formPerm [5, 6]
  | 1 => List.formPerm [0, 2] * List.formPerm [1, 9] * List.formPerm [3, 6] * List.formPerm [4, 10]
  | 2 => List.formPerm [0, 9] * List.formPerm [1, 7] * List.formPerm [2, 8] * List.formPerm [5, 10]

@[expose] def m11WordA : List (Fin 3) := [0, 2, 0, 1, 2, 1, 0, 2, 0, 2, 1, 0, 1, 2]

@[expose] def m11WordB : List (Fin 3) := [1, 0, 2, 1, 2, 1, 2, 0, 2, 0, 1, 2, 0]

end CFSG.QuasithinUnique.Setup.X1
