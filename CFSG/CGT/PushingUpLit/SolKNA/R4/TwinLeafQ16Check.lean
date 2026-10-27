module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data qGens qCert)

@[expose] def q16q16Free (n : ℕ) (pts sq fo : Array (Array ℕ)) : Bool :=
  allLt pts.size fun i =>
    eqA n fo[i]! (idA n) || !eqA n (compA n fo[i]! fo[i]!) (idA n) ||
      allLt pts.size fun j =>
        !eqA n sq[j]! fo[i]! ||
          !eqA n (compA n pts[j]! pts[i]!) (compA n (invCand n pts[i]!) pts[j]!) ||
          allLt pts.size fun k =>
            !eqA n fo[k]! fo[i]! ||
              !eqA n (compA n pts[i]! pts[k]!) (compA n pts[k]! pts[i]!) ||
              !eqA n (compA n pts[j]! pts[k]!) (compA n pts[k]! pts[j]!) ||
              allLt pts.size fun l =>
                !eqA n sq[l]! fo[k]! ||
                  !eqA n (compA n pts[l]! pts[k]!) (compA n (invCand n pts[k]!) pts[l]!) ||
                  !eqA n (compA n pts[i]! pts[l]!) (compA n pts[l]! pts[i]!) ||
                  !eqA n (compA n pts[j]! pts[l]!) (compA n pts[l]! pts[j]!)

@[expose] def q16q16Check' (X : Q16Data) (qg : Array (Array ℕ)) (cQ : ArrCert) : Bool :=
  allLt X.pg.size (fun k => validA X.n X.pg[k]!) &&
  X.qKeys.all (fun p => decide (p < X.n)) &&
  X.qW.all (fun w => w.all fun l => decide (l < X.pg.size)) &&
  enumOK X.n qg X.qKeys cQ && cQ.pts.size == X.qOrd &&
  q16q16Free X.n cQ.pts (cQ.pts.map fun y => compA X.n y y)
    ((cQ.pts.map fun y => compA X.n y y).map fun y => compA X.n y y)

@[expose] def q16q16Check (X : Q16Data) : Bool := q16q16Check' X (qGens X) (qCert X)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Check
