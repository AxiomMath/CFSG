module

public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B.CTIB.Native

@[expose] def innerImgs (d : Nat) : Array Nat :=
  ((List.range 22).map fun i => qmul gArr (qmul gArr (qinv d) (2 ^ i)) d).toArray

@[expose] def isLetterB (l : Int) : Bool := l == 1 || l == -1 || l == 2 || l == -2

@[expose] def oddWitOK (c y : Nat) (wa : List Int) (ea ma : Nat) (wb : List Int) (eb mb n e : Nat) :
    Bool :=
  let gi := genInvImgs ()
  let A := wordAut gi wa
  let B := wordAut gi wb
  let Ae := autPow gArr A ea
  let Be := autPow gArr B eb
  let Aa := autPow gArr Ae (ma + 1)
  let Bb := autPow gArr Be (mb + 1)
  let S := autComp gArr (autComp gArr (autComp gArr (autComp gArr (autComp gArr Aa Bb)
    (autPow gArr Aa (ma - 1))) (innerImgs n)) Aa) (innerImgs (qinv n))
  wa.all isLetterB && wb.all isLetterB && ma % 2 == 1 && mb % 2 == 1 &&
    autPow gArr Ae ma == id23 && autPow gArr Be mb == id23 &&
    autApply gArr A c == c && autApply gArr A y == y &&
    autApply gArr B c == c && autApply gArr B y == y &&
    qmul gArr n c == qmul gArr c n && qmul gArr n y == qmul gArr y n &&
    autComp gArr S S == innerImgs y &&
    qmul gArr e c == qmul gArr c e && qmul gArr (qmul gArr (qinv e) y) e == qmul gArr y (2 ^ 22)

@[expose] def wordY2a : List Int :=
  [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 2, 2, 2, 2, 2, 2,
    1, -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2,
    2, 2, 1, 2, 1]

@[expose] def wordY2b : List Int :=
  [1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 1, -2, -2, -2, 1, 2, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, -2, -2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2,
    1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, -2, 1, -2, 1, -2, -2,
    1, -2, 1, -2, 1, 2, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, -2, -2]

@[expose] def wordCY2a : List Int :=
  [-2, -2, -2, -2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, -2, -2,
    1, 2, 2, 2, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2,
    1, 2, 2, 2, 2, 2, 1, -2, -2, -2, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, -2]

@[expose] def wordCY2b : List Int :=
  [-2, -2, -2, -2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2,
    2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, -2, -2, -2, -2, -2,
    1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, -2]

@[expose] def wordY3a : List Int :=
  [1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 2, 2, 1, -2, -2, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 2, 1, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1,
    -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2, -2, -2, -2, -2, 1, 2, 2, 2, 1,
    2, 1, -2, -2]

@[expose] def wordY3b : List Int :=
  [2, 1, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
    -2, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2,
    -2, 1, -2, 1, -2, -2, -2, -2, 1, 2, 2, 2, 1, 2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, -2, -2, -2,
    -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 2, 2, 1, -2, -2, -2, -2, 1, 2, 2, 2, 1,
    -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1]

@[expose] def frameCodesOK : Bool :=
  qmul gArr 1 6 == 7 && qmul gArr 6 1 == 7 && qmul gArr 1 7 == 6 && qmul gArr 7 1 == 6

end CFSG.EvenSmallLie.TwoE6
