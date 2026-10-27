module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Ch1.Six
open Equiv Equiv.Perm

@[expose] def a6 : Perm (Fin 6) := swap 0 2 * swap 4 5

end CFSG.QuasithinUnique.Ch1.Six

namespace CFSG.QuasithinUnique.Ch1.Seven
open Equiv Equiv.Perm

@[expose] def a7 : Perm (Fin 7) := swap 0 2 * swap 4 5

end CFSG.QuasithinUnique.Ch1.Seven
