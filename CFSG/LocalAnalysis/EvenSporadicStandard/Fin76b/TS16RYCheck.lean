module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.S16

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def j2Hex : String := include_str "TS16RYJ2.txt"

@[expose] def j3Hex : String := include_str "TS16RYJ3.txt"

@[expose] def j2Tb (k : ℕ) : Table := hexT 3 315 (315 * k) j2Hex

@[expose] def j3Tb (k : ℕ) : Table := hexT 4 6156 (6156 * k) j3Hex

@[expose] def quadIn (n : ℕ) (t x y : Table) : Bool :=
  tblEq n y (idT n) || tblEq n y t || tblEq n y x || tblEq n y (compT n t x)

@[expose] def quadCheck (n cap : ℕ) (cs : List Table) (t x : Table) : Bool :=
  (mulClosureH n cs.toArray cap).1.all fun a =>
    invOK n a (invT n a) && quadIn n t x (compT n a a) &&
      (mulClosureH n cs.toArray cap).1.all fun b =>
        quadIn n t x (compT n (compT n a b) (compT n (invT n a) (invT n b)))

@[expose] def cTbls (n : ℕ) (r : Table) (es : List Table) (flags : List Bool) : List Table :=
  (es.zip flags).map fun p => if p.2 then compT n p.1 r else p.1

@[expose] def s16Check (n cap : ℕ) (sift : Table → Bool) (uT tT bT rT vT xT : Table)
    (rootsL es : List Table) (flags : List Bool) : Bool :=
  permOK n uT && permOK n tT && permOK n bT && permOK n rT && permOK n vT && permOK n xT &&
  rootsL.all (permOK n) && es.all (permOK n) &&
  sift tT && sift bT && sift vT && sift xT && rootsL.all sift && es.all sift &&
  sift (compT n rT uT) && !sift rT &&
  invoOK n rT && tblEq n (compT n (compT n rT tT) rT) tT &&
  invOK n bT (invT n bT) && tblEq n (compT n (compT n rT bT) rT) (invT n bT) &&
  commTT n vT tT && commTT n xT tT && tblEq n (powT n 4 vT) tT &&
  tblEq n (powT n 8 vT) (idT n) && invoOK n xT && !tblEq n xT (idT n) && !tblEq n xT tT &&
  invOK n vT (invT n vT) && tblEq n (compT n (compT n xT vT) xT) (invT n vT) &&
  tblEq n (compT n (compT n rT vT) rT) (compT n vT tT) &&
  tblEq n (compT n (compT n rT xT) rT) (compT n xT tT) &&
  tblEq n (compT n (compT n vT bT) (invT n vT)) (invT n bT) &&
  tblEq n (compT n (compT n xT bT) xT) (invT n bT) &&
  rootsL.all (fun z => tblEq n (compT n z z) tT) && enumOK n cap 32 rootsL &&
  centCount n cap rootsL [rT] == 8 &&
  permOK n (compT n vT vT) && permOK n (compT n vT xT) &&
  enumOK n cap 8 [compT n vT vT, compT n vT xT] &&
  memT n (mulClosureH n rootsL.toArray cap).1 (compT n vT vT) &&
  memT n (mulClosureH n rootsL.toArray cap).1 (compT n vT xT) &&
  commTT n (compT n vT vT) rT && commTT n (compT n vT xT) rT &&
  enumOK n cap 32 [vT, xT, rT] &&
  es.all (fun e => commTT n e tT) &&
  (cTbls n rT es flags).all (permOK n) && enumOK n cap 32 (cTbls n rT es flags) &&
  (cTbls n rT es flags).all (fun c => commTT n c xT) &&
  memT n (mulClosureH n (cTbls n rT es flags).toArray cap).1 tT &&
  memT n (mulClosureH n (cTbls n rT es flags).toArray cap).1 xT &&
  quadCheck n cap (cTbls n rT es flags) tT xT

end CFSG.EvenSporadicStandard.Fin76b.S16
