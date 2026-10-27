module

public import CFSG.Sporadic.J4.QT2LocX0NNative

public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def eW (ws : List (List Int)) (m : Nat) : List Int :=
  (List.range 4).flatMap fun k => if m.testBit k then ws.getD k [] else []

@[expose] def eTab (ws : List (List Int)) : Array (Array V2) :=
  Array.ofFn (n := 16) fun i => wR (eW ws i.val)

@[expose] def eR (ws : List (List Int)) (m : Nat) : Array V2 := (eTab ws)[m]!

@[expose] def xR : Array V2 := x0GenRows[0]!

@[expose] def eList (ws : List (List Int)) : List (Array V2) :=
  let T := eTab ws
  (List.range 16).map fun m => T[m]!

@[expose] def chkGrp (ws : List (List Int)) : Bool :=
  let E := eTab ws
  ws.length == 4 && (List.range 16).all (fun m => wfR E[m]!) &&
    eqRows E[0]! idRows && allDistinct ((List.range 16).map fun m => E[m]!) &&
    (List.range 16).all (fun m => (List.range 16).all fun m' =>
      eqRows (mulRows E[m]! E[m']!) E[m ^^^ m']!) &&
    (List.range 4).all fun k => eqRows (wR (ws.getD k [])) E[2 ^ k]!

@[expose] def chkNorm (ws : List (List Int)) : Bool :=
  let E := eTab ws
  (List.range 16).all (fun m => (List.range 16).any fun m' =>
    eqRows (mulRows xR E[m]!) (mulRows E[m']! xR)) &&
    (List.range 15).all fun m => !eqRows (mulRows xR E[m + 1]!) (mulRows E[m + 1]! xR)

@[expose] def ordRows (M : Array V2) (r : Nat) : Bool :=
  !eqRows M idRows && eqRows (powRows M r) idRows

@[expose] def chkK0 (ws : List (List Int)) : Bool :=
  let G := (List.range 4).map fun k => wR (ws.getD k [])
  (List.range 6720).all fun q =>
    let M := x0Orb.mats[q]!
    !(G.all fun g => eqRows (mulRows M g) (mulRows g M)) ||
      (!ordRows M 3 && !ordRows M 7 && !ordRows M 23)

@[expose] def chkNcore (E : List (Array V2)) : Bool :=
  (List.range 6720).any fun q =>
    (List.range 3).any fun i =>
      let n := mulRows x0Orb.mats[q]! (powRows nRows (i + 1))
      (E.all fun e => let ne := mulRows n e; E.any fun e' => eqRows ne (mulRows e' n)) &&
        [2, 3, 4].any fun j => eqRows (mulRows n xR) (mulRows (powRows xR j) n)

@[expose] def chkN (ws : List (List Int)) : Bool := chkNcore (eList ws)

@[expose] def chkW (ws : List (List Int)) (Q : Array V2) : Bool :=
  let E := eTab ws
  let QI := invRows Q
  wfR Q && wfR QI && eqRows (mulRows Q QI) idRows &&
    ((List.range 16).all fun m => eqRows (mulRows Q E[m]!) (mulRows E[m]! Q)) &&
    allDistinct (((List.range 16).map fun m => mulRows (mulRows E[m]! xR) E[m]!) ++
      [mulRows (mulRows Q xR) QI])

@[expose] def chkAll (ws : List (List Int)) (Q : Array V2) : Bool :=
  chkGrp ws && chkNorm ws && chkK0 ws && chkN ws && chkW ws Q

end CFSG.QuasithinUnique.A5.Dec2
