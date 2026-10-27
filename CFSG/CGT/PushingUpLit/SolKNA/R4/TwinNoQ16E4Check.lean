module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Check

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)

structure Q16Data where
  n : ℕ
  pg : Array (Array ℕ)
  qW : Array (List ℕ)
  qKeys : List ℕ
  qFuel : ℕ
  qOrd : ℕ

@[expose] def qGens (X : Q16Data) : Array (Array ℕ) := X.qW.map (posWord X.n X.pg)

@[expose] def qCert (X : Q16Data) : ArrCert := enumBfs X.n (qGens X) X.qKeys X.qFuel

@[expose] def q16Free (n : ℕ) (pts sq : Array (Array ℕ)) : Bool :=
  allLt pts.size fun i =>
    eqA n (compA n sq[i]! sq[i]!) (idA n) ||
      !eqA n (compA n (compA n sq[i]! sq[i]!) (compA n sq[i]! sq[i]!)) (idA n) ||
      allLt pts.size fun j =>
        !eqA n sq[j]! (compA n sq[i]! sq[i]!) ||
          !eqA n (compA n pts[j]! pts[i]!) (compA n (invCand n pts[i]!) pts[j]!)

@[expose] def q16Check' (X : Q16Data) (qg : Array (Array ℕ)) (cQ : ArrCert) : Bool :=
  allLt X.pg.size (fun k => validA X.n X.pg[k]!) &&
  X.qKeys.all (fun p => decide (p < X.n)) &&
  X.qW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  enumOK X.n qg X.qKeys cQ && cQ.pts.size == X.qOrd &&
  q16Free X.n cQ.pts (cQ.pts.map fun y => compA X.n y y)

@[expose] def q16Check (X : Q16Data) : Bool := q16Check' X (qGens X) (qCert X)

end CFSG.CGT.PushingUpLit.SolKNA.R4.Check
