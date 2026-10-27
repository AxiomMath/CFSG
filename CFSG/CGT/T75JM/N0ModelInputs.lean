module

public import CFSG.CGT.T75JM.Interfaces
public import CFSG.CGT.T75JM.M22PresTables

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def n0Tab (w : List (Fin 6 × Bool)) : Table :=
  wordT 22 m22L ((liftWord w).map m22LetterZ)

@[expose] def n0InvCheck : Bool := (List.range 6).all fun k => invOK 22 (m22T k) (m22V k)

@[expose] def n0RelCheck : Bool := rels6.all fun r => n0Tab r == idT 22

end CFSG.CGT.T75JM
