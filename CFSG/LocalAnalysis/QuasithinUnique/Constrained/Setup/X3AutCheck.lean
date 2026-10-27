module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutData

public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique.A6Facts.Core

set_option maxRecDepth 100000

@[expose] def invC (c : List Nat) : List Nat := (List.range 10).map fun j => c.idxOf j

@[expose] def isInvC (c : List Nat) : Bool := cmul c c == cid && c != cid

@[expose] def invsC : List (List Nat) := autL.filter isInvC

@[expose] def commAll (c : List Nat) (E : List (List Nat)) : Bool :=
  E.all fun e => cmul c e == cmul e c

@[expose] def rep (j : Nat) : List (List Nat) := repsC.getD j []

@[expose] def keysC : List (Nat × List Nat) :=
  (List.range repsC.length).flatMap fun j =>
    (invsC.filter fun c => !(rep j).contains c && commAll c (rep j)).map fun c => (j, c)

@[expose] def stepOK (key : Nat × List Nat) (ent : Nat × Nat) : Bool :=
  let E := rep key.1
  let n := autL.getD ent.1 cid
  let ni := invC n
  let Ek := rep ent.2
  ((E ++ [key.2]).all fun e => Ek.contains (cmul (cmul n e) ni)) && Ek.length == 2 * E.length

@[expose] def stepCheck : Bool :=
  keysC.length == stepTbl.length && (keysC.zip stepTbl).all (fun p => stepOK p.1 p.2) &&
    keysC.all fun key => (rep key.1).length < 8

@[expose] def repOK (E : List (List Nat)) (r : Nat) : Bool :=
  decide E.Nodup && E.contains cid && E.length == 2 ^ r &&
    E.all (fun e => autL.contains e && cmul e e == cid) &&
    E.all fun e => E.all fun f => cmul e f == cmul f e && E.contains (cmul e f)

@[expose] def repsCheck : Bool :=
  repsC.length == repRank.length && ((repsC.zip repRank).all fun p => repOK p.1 p.2) &&
    repRank.all (fun r => r ≤ 3) && repsC.getD 0 [] == [cid]

@[expose] def evalWord (X : List (List Nat)) (w : List Nat) : List Nat :=
  w.foldl (fun acc i => cmul acc (X.getD i cid)) cid

@[expose] def witX (E : List (List Nat)) (S : List Nat) : List (List Nat) :=
  (S.map fun i => pslLit.getD i cid).flatMap fun s => E.map fun e => cmul (cmul s e) (invC s)

@[expose] def witOK (E : List (List Nat)) (r : Nat) (S : List Nat) (W : List (List Nat)) : Bool :=
  S.all (fun i => i < pslLit.length) && decide (S.length * r ≤ 6) && W.length == pslGenC.length &&
    (pslGenC.zip W).all fun p => evalWord (witX E S) p.2 == p.1

@[expose] def witCheck : Bool :=
  witS.length == repsC.length && witW.length == repsC.length &&
    (List.range repsC.length).all fun j =>
      repRank.getD j 0 == 0 || witOK (rep j) (repRank.getD j 0) (witS.getD j []) (witW.getD j [])

@[expose] def pslInvs : List (List Nat) := pslLit.filter isInvC

@[expose] def d3Check : Bool :=
  d3H.length == pslInvs.length && d3A0 < pslLit.length &&
    ((pslInvs.zip d3H).all fun p =>
      p.2 < pslLit.length &&
        cmul (cmul (pslLit.getD p.2 cid) (pslLit.getD d3A0 cid)) (invC (pslLit.getD p.2 cid)) == p.1) &&
    isInvC (pslLit.getD d3A0 cid) && d3G.length == 3 && d3G.all (fun i => i < pslLit.length) &&
    d3W.length == pslGenC.length &&
    (pslGenC.zip d3W).all fun p =>
      evalWord (d3G.map fun i =>
        cmul (cmul (pslLit.getD i cid) (pslLit.getD d3A0 cid)) (invC (pslLit.getD i cid))) p.2 == p.1

theorem repsCheck_true : repsCheck = true := by decide +kernel

theorem stepCheck_true : stepCheck = true := by decide +kernel

theorem witCheck_true : witCheck = true := by decide +kernel

theorem d3Check_true : d3Check = true := by decide +kernel

end CFSG.QuasithinUnique.Setup.X3Aut
