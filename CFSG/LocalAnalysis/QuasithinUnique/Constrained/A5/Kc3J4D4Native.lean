module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Native

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def d4El (w : List Int) : List Int := w.map fun l => if 0 < l then l + 3 else l - 3

@[expose] def d4EtaTabs : Array (Array V2) := (Array.range 2048).map fun c => frTable (etaE c)

@[expose] def d4Fix (c : Nat) (u : V2) : Bool := (frApply d4EtaTabs[c]! u).beq u

@[expose] def d4Us (r : V2) (Pi : Array V2) : List V2 :=
  let tX := frTable (x0InvRows[0]!)
  let tP := frTable Pi
  let a1 := frApply tX r
  let a2 := frApply tX a1
  let a3 := frApply tX a2
  let a4 := frApply tX a3
  [frApply tP a1, frApply tP a2, frApply tP a3, frApply tP a4]

@[expose] def d4Estab (us : List V2) : List Nat :=
  (List.range 2048).filter fun c => c != 0 && us.all (d4Fix c)

@[expose] def d4Conj (T : Array V2) : Array V2 :=
  mulRows (mulRows (x0GenRows[0]!) T) (x0InvRows[0]!)

@[expose] def d4Sub (ts : List (Array V2)) (m : Nat) : Array V2 :=
  (List.range 4).foldl (fun acc i => if m.testBit i then mulRows acc (ts.getD i #[]) else acc)
    idRows

@[expose] def d4ConjOK (ts : List (Array V2)) (E : Array (Array V2)) (K : Array V2) : Bool :=
  let S := (List.range 16).map (d4Sub ts)
  eqRows (S.getD 0 #[]) idRows &&
    (List.range 16).all (fun m => (List.range 4).all fun g =>
      S.any fun s' => eqRows (mulRows (S.getD m #[]) (ts.getD g #[])) s') &&
    (List.range 16).all fun m => S.any fun s' => eqRows (mulRows K (E[m]!)) (mulRows s' K)

@[expose] def d4Rest (wit : List (Nat × Nat × Nat × Nat)) (Es : List (Array (Array V2)))
    (i c : Nat) (T : Array V2) : Bool :=
  !eqRows (mulRows T (d4Conj T)) (mulRows (d4Conj T) T) ||
    !eqRows (mulRows T (d4Conj (d4Conj T))) (mulRows (d4Conj (d4Conj T)) T) ||
      match wit.find? (fun w => w.1 == i && w.2.1 == c) with
      | none => false
      | some w =>
        w.2.2.1 < 2 && w.2.2.2 < 6720 &&
          d4ConjOK [T, d4Conj T, d4Conj (d4Conj T), d4Conj (d4Conj (d4Conj T))]
            (Es.getD w.2.2.1 #[]) (x0Orb.mats[w.2.2.2]!)

@[expose] def d4PairOK (wit : List (Nat × Nat × Nat × Nat)) (Es : List (Array (Array V2)))
    (i c : Nat) (P Pi : Array V2) (ptsP : List V2) : Bool :=
  ptsP.any (d4Fix c) || d4Rest wit Es i c (mulRows (mulRows Pi (etaE c)) P)

@[expose] def d4Pts : List V2 := x0Pts.eraseDups

@[expose] def d4RepOK (wit : List (Nat × Nat × Nat × Nat)) (Es : List (Array (Array V2)))
    (i : Nat) (r : V2) (w : List Int) : Bool :=
  let P := wR (d4El w)
  let Pi := wR (invWord (d4El w))
  r.wf && wfRows P && wfRows Pi && (frApply (frTable P) rootV).beq r &&
    (let ptsP := d4Pts.map (frApply (frTable Pi))
     (d4Estab (d4Us r Pi)).all fun c => d4PairOK wit Es i c P Pi ptsP)

@[expose] def chkD4 (reps : Array V2) (words : List (List Int))
    (wit : List (Nat × Nat × Nat × Nat)) (vs : List (List (List Int))) : Bool :=
  reps.size == words.length && vs.length == 2 && wfRows idRows &&
    (List.range 2048).all (fun c => wfRows (etaE c)) &&
    (let Es := vs.map Dec2.eTab
     (List.range reps.size).all fun i => d4RepOK wit Es i reps[i]! (words.getD i []))

end CFSG.QuasithinUnique.A5
