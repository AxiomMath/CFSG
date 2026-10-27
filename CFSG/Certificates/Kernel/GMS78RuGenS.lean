module

public import Certificates.Data.GMS78RuSPrimeCheck

public section

namespace CFSG.KC.GMS.Gen

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS CFSG.GMS78RuSP

section S

variable (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8)

@[expose] def sMulFG (ε : Bool) (p q : Nat × Fin 8 × Fin 8) : Nat × Fin 8 × Fin 8 :=
  let dp := dA.getD (256 * p.2.2.val + q.1) (0, 0)
  (p.1 ^^^ dp.1,
    p.2.1 ^^^ linApply (dct.getD p.2.2.val linId) q.2.1 ^^^ dp.2 ^^^ gA.getD (256 * p.1 + dp.1) 0 ^^^
      (if ε && dOvf p.2.2 q.2.2 then 1 else 0),
    dMul p.2.2 q.2.2)

@[expose] def mul16G (ε : Bool) (p q : Nat) : Nat := enc16 (sMulFG gA dA dct ε (lift16 p) (lift16 q))

@[expose] def inv16G (ε : Bool) : List Nat :=
  (List.range 2048).filter fun u => mul16G gA dA dct ε u u == 0 && u != 0 && u != 256

@[expose] def cent16G (ε : Bool) (u : Nat) : List Nat :=
  (List.range 2048).filter fun p => mul16G gA dA dct ε p u == mul16G gA dA dct ε u p

@[expose] def cntR16G (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => mul16G gA dA dct ε p p == t

@[expose] def key16G (ε : Bool) (u : Nat) : Nat × Nat × Nat × Nat :=
  let C := cent16G gA dA dct ε u
  (u, C.length, cntR16G gA dA dct ε C u, cntR16G gA dA dct ε C 256)

@[expose] def conjSq16G (ε : Bool) (u : Nat) : Bool :=
  (cent16G gA dA dct ε u).any fun p => mul16G gA dA dct ε p p != 0 &&
    (List.range 2048).any fun w => mul16G gA dA dct ε w u ==
      mul16G gA dA dct ε (mul16G gA dA dct ε u (mul16G gA dA dct ε p p)) w

@[expose] def check16G (ε : Bool) : Bool :=
  let K := (inv16G gA dA dct ε).map (key16G gA dA dct ε)
  (K.all fun a => K.all fun b =>
    !(a.2.1 == b.2.1 && a.2.2.1 == b.2.2.2 && a.2.2.2 == b.2.2.1) || a.2.1 == 128) &&
  (K.all fun a => a.2.1 != 128 || conjSq16G gA dA dct ε a.1) &&
  ((List.range 2048).all fun p => mul16G gA dA dct ε 256 (mul16G gA dA dct ε p p) / 512 == 0) &&
  (K.all fun a => a.1 / 512 != 0 || a.2.1 != 128) &&
  ((List.range 2048).all fun p => mul16G gA dA dct ε p 256 == mul16G gA dA dct ε 256 p)

@[expose] def mul17G (ε : Bool) (p q : Nat) : Nat := enc17 (sMulFG gA dA dct ε (lift17 p) (lift17 q))

@[expose] def inv17G (ε : Bool) : List Nat :=
  (List.range 8192).filter fun u => mul17G gA dA dct ε u u == 0 && u != 0 && u != 256

@[expose] def cent17G (ε : Bool) (u : Nat) : List Nat :=
  (List.range 8192).filter fun p => mul17G gA dA dct ε p u == mul17G gA dA dct ε u p

@[expose] def cntR17G (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => mul17G gA dA dct ε p p == t

@[expose] def zx17G (ε : Bool) (C : List Nat) (t : Nat) : Nat :=
  C.countP fun p => C.all fun q =>
    mul17G gA dA dct ε p q == mul17G gA dA dct ε q p ||
      mul17G gA dA dct ε p q == mul17G gA dA dct ε t (mul17G gA dA dct ε q p)

@[expose] def key17G (ε : Bool) (u : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let C := cent17G gA dA dct ε u
  let r := cntR17G gA dA dct ε C u
  let r' := cntR17G gA dA dct ε C 256
  (u, C.length, r, r',
    if needZ17 u C.length r r' then zx17G gA dA dct ε C u else 0,
    if needZ17 u C.length r r' then zx17G gA dA dct ε C 256 else 0)

@[expose] def check17G (ε : Bool) : Bool :=
  let K := (inv17G gA dA dct ε).map (key17G gA dA dct ε)
  ((List.range 8192).all fun p => mul17G gA dA dct ε p 256 == mul17G gA dA dct ε 256 p) &&
  K.all fun a => inX17 a.1 || K.all fun b =>
    !(a.2.1 == b.2.1 && a.2.2.1 == b.2.2.2.1 && a.2.2.2.1 == b.2.2.1) ||
      (a.2.1 == 128 && (a.1 / 1024 == 1 || a.1 / 1024 == 5)) ||
      (needZ17 a.1 a.2.1 a.2.2.1 a.2.2.2.1 && needZ17 b.1 b.2.1 b.2.2.1 b.2.2.2.1 &&
        (a.2.2.2.2.1 != b.2.2.2.2.2 || a.2.2.2.2.2 != b.2.2.2.2.1))

variable (xs : List Pt)

@[expose] def pMulG (p q : Pt) : Pt := sMulFG gA dA dct true p q

@[expose] def sqPtG (p : Pt) : Pt := pMulG gA dA dct p p

@[expose] def inJG (p : Pt) : Bool :=
  xs.all fun x => pMulG gA dA dct p x == pMulG gA dA dct x p ||
    pMulG gA dA dct p x == pMulG gA dA dct fPt (pMulG gA dA dct x p)

@[expose] def inCXG (p : Pt) : Bool := xs.all fun x => pMulG gA dA dct p x == pMulG gA dA dct x p

@[expose] def jPtsG : List Pt := allPt.filter (inJG gA dA dct xs)

@[expose] def jMemG (p : Pt) : Bool :=
  if encPt p < 16384 then inJG gA dA dct xs (decPt (encPt p)) else false

@[expose] def cmtG (q p : Pt) : Bool := pMulG gA dA dct p q == pMulG gA dA dct q p

@[expose] def checkAG : Bool :=
  inJG gA dA dct xs aPt && !inCXG gA dA dct xs aPt && sqPtG gA dA dct aPt == onePt

@[expose] def checkCaG : Bool := allPt.countP (cmtG gA dA dct aPt) == 1024

@[expose] def checkCxG : Bool :=
  (jPtsG gA dA dct xs).all fun x => inCXG gA dA dct xs x || sqPtG gA dA dct x != onePt ||
    decide ((jPtsG gA dA dct xs).countP (cmtG gA dA dct x) ≤ 128)

@[expose] def checkF1G : Bool :=
  allPt.all fun y => !cmtG gA dA dct aPt y || !jMemG gA dA dct xs (sqPtG gA dA dct y) ||
    jMemG gA dA dct xs y || evenD y.2.2 ||
    (jPtsG gA dA dct xs).any fun j => cmtG gA dA dct aPt j &&
      sqPtG gA dA dct (pMulG gA dA dct y j) == onePt

@[expose] def checkF3G : Bool :=
  inJG gA dA dct xs cPt && !inCXG gA dA dct xs cPt &&
    ((jPtsG gA dA dct xs).filter (inCXG gA dA dct xs)).all fun k =>
    sqPtG gA dA dct (pMulG gA dA dct k cPt) != onePt || allPt.any fun u =>
      cmtG gA dA dct (pMulG gA dA dct k cPt) u && jMemG gA dA dct xs (sqPtG gA dA dct u) &&
      !jMemG gA dA dct xs u && !evenD u.2.2 &&
        (jPtsG gA dA dct xs).all fun j => !cmtG gA dA dct (pMulG gA dA dct k cPt) j ||
          sqPtG gA dA dct (pMulG gA dA dct u j) != onePt

@[expose] def checkJdG : Bool :=
  ([0, 1, 4, 5] : List (Fin 8)).all fun d => (jPtsG gA dA dct xs).any fun j => j.2.2 == d

end S

end CFSG.KC.GMS.Gen

end
