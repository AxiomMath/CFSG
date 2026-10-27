
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Inputs

public section

namespace CFSG.QuasithinUnique.L246.C123
open Equiv

@[expose] def c5 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def c7 : Perm (Fin 7) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

@[expose] def pset5 : Finset (Perm (Fin 7)) := {1, c5, c5 ^ 2, c5 ^ 3, c5 ^ 4}

@[expose] def pset7 : Finset (Perm (Fin 7)) :=
  {1, c7, c7 ^ 2, c7 ^ 3, c7 ^ 4, c7 ^ 5, c7 ^ 6}

end CFSG.QuasithinUnique.L246.C123
