module

public import CFSG.CGT.T75M23.M23PresTables

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def n7GenT : Array Table := #[m23T 0, m23T 1, m23T 2, m23T 3, m23T 4, m23T 5]

@[expose] def n7GenV : Array Table := #[m23V 0, m23V 1, m23V 2, m23V 3, m23V 4, m23V 5]

@[expose] def n7L (z : ℤ) : Table :=
  if 0 < z then n7GenT[(z - 1).toNat]! else n7GenV[(-z - 1).toNat]!

@[expose] def n7Tab (w : List (Fin 6 × Bool)) : Table :=
  wordT 23 n7L ((liftWord7 w).map m23LetterZ)

@[expose] def n7InvCheck : Bool := (List.range 6).all fun k => invOK 23 n7GenT[k]! n7GenV[k]!

@[expose] def n7RelCheck : Bool := rels7.all fun r => n7Tab r == idT 23

end CFSG.CGT.T75M23
