module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.Sporadic.J4.QT2LocFiveNative
public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.Sporadic.J4.QT2.B7

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def rep5Vec : V2 := pathVec (repPaths.getD 5 [])

@[expose] def orb5 : VOrb := vorbit locTabs rep5Vec 15180 15

@[expose] def uRows : Array (Array V2) := uTab (locMats ()) (locInvs ())

@[expose] def xiInv : Array V2 := invRows fiveRows

@[expose] def conjXi (T : Array V2) : Array V2 := mulRows (mulRows fiveRows T) xiInv

@[expose] def vRows (t0 : Array V2) : Array (Array V2) :=
  let t1 := conjXi t0
  let t2 := conjXi t1
  #[t0, t1, t2, conjXi t2]

@[expose] def prodRows (Vs : Array (Array V2)) (k : Nat) : Array V2 := etaRows Vs 4 k

@[expose] def neId (M : Array V2) : Bool :=
  (List.range 112).any fun i => differs (M[i]?.getD V2.zero) (idRows[i]?.getD V2.zero)

@[expose] def fixedBy (VT : Array (Array V2)) (q : V2) : Bool :=
  (List.range 4).all fun i => !(differs (frApply (VT[i]?.getD #[]) q) q)

@[expose] def etaTab : Array (Array V2) := (Array.range 2048).map fun c => etaRows uRows 11 c

@[expose] def actTabOK (Mq Mqi : Array V2) (t : List Nat) : Bool :=
  t.length == 11 && (List.range 11).all fun j =>
    decide (t.getD j 0 < 2048) &&
      eqRows (mulRows (mulRows Mq (uRows[j]?.getD idRows)) Mqi) etaTab[t.getD j 0]!

@[expose] def chkB7V (T0 : Array V2) (g0w : List Int) (c0 : Nat) : Bool :=
  let Vs := vRows T0
  let G0 := wR g0w
  let G0i := invRows G0
  eqRows (mulRows fiveRows xiInv) idRows &&
    (List.range 4).all (fun i =>
      eqRows (mulRows (Vs[i]?.getD idRows) (Vs[i]?.getD idRows)) idRows) &&
    (List.range 4).all (fun i => (List.range 4).all fun j =>
      eqRows (mulRows (Vs[i]?.getD idRows) (Vs[j]?.getD idRows))
        (mulRows (Vs[j]?.getD idRows) (Vs[i]?.getD idRows))) &&
    eqRows (conjXi (Vs[3]?.getD idRows)) (prodRows Vs 15) &&
    !(differs (frApply (frTable (Vs[0]?.getD idRows)) rootV) rootV) &&
    eqRows (mulRows G0 G0i) idRows && tMasks.contains c0 && decide (c0 < 2048) &&
    eqRows (mulRows (mulRows G0i (Vs[0]?.getD idRows)) G0) etaTab[c0]!

@[expose] def chkCross (A B : Array (Array V2)) : Bool :=
  (List.range 4).all fun j =>
    (List.range 16).any fun k => eqRows (A[j]?.getD idRows) (etaRows B 4 k)

end CFSG.Sporadic.J4.QT2.B7
