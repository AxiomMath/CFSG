module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

@[expose] def sqOneB (g : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => g (g i) == i

@[expose] def cubeOneB (g : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => g (g (g i)) == i

@[expose] def isOneB (g : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => g i == i

@[expose] def commB (a b : Equiv.Perm (Fin 28)) : Bool :=
  (List.finRange 28).all fun i => a (b i) == b (a i)

@[expose] def order3B (g : Equiv.Perm (Fin 28)) : Bool := cubeOneB g && !isOneB g

@[expose] def centList (LP : List (Equiv.Perm (Fin 28))) (g : Equiv.Perm (Fin 28)) :
    List (Equiv.Perm (Fin 28)) :=
  LP.filter (commB g)

@[expose] def cent3OddB (LA LP : List (Equiv.Perm (Fin 28))) (g : Equiv.Perm (Fin 28)) : Bool :=
  !(order3B g) || (centList LP g).length % 2 == 1 ||
    LA.all fun σ => !(sqOneB σ && commB σ g) || QP.sift σ 0

@[expose] def cent3OddAll (LA LP : List (Equiv.Perm (Fin 28))) : Bool :=
  LP.all (cent3OddB LA LP)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
