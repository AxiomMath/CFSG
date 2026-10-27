module

public import CFSG.CGT.L5R.R3Data
public import CFSG.CGT.M24R.L2Inputs

public section

namespace CFSG.CGT.L5R.R3

open CFSG.CGT.M24R CFSG.Sporadic.Th.Native

@[expose] def tEq (w w' : N0Word) : Bool := wTab w == wTab w'

@[expose] def identCheck : Bool :=
  tEq (thExp uD) (dExp uD) && tEq (nW ++ dExp uD ++ inv10 nW) bW && tEq (dExp bD) bW &&
    tEq (thExp bD) dAW && !tEq dAW [] &&
    (List.finRange 2).all fun j =>
      tEq (dExp (yD j)) (yW j) && tEq (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) &&
        tEq (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) && tEq (thExp (b1D j)) (fW j) &&
        tEq (inv10 wW ++ yW j ++ wW) (fW j)

@[expose] def centCheck (cx : Ctx8) : Bool :=
  let Y₁ := wTab (yW 0)
  let Y₂ := wTab (yW 1)
  cx.codes.all fun c => let X := cx.tab c; !(commT X Y₁ && commT X Y₂) || X == idT 16

end CFSG.CGT.L5R.R3
