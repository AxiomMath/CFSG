module

public import CFSG.Sporadic.J4.QT2LocZCentNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZClNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZTabNative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def zXi : Array V2 := x0GenRows[0]!

@[expose] def zXiInv : Array V2 := x0InvRows[0]!

@[expose] def zXiConj (T : Array V2) : Array V2 := mulRows (mulRows zXi T) zXiInv

@[expose] def zCjRows (T : Array V2) : Nat → Array V2
  | 0 => T
  | n + 1 => zXiConj (zCjRows T n)

@[expose] def zConjBy (gW : List Int) (T : Array V2) : Array V2 :=
  mulRows (mulRows (wR gW) T) (wR (invW gW))

@[expose] def zMsN (T₀ : Array V2) (gW : List Int) : Nat → Array V2
  | 0 => etaE 1
  | n + 1 => zConjBy gW (zCjRows T₀ (n + 1))

@[expose] def zMs (T₀ : Array V2) (gW : List Int) (i : Fin 4) : Array V2 := zMsN T₀ gW i

@[expose] def zYR (gW : List Int) : Array V2 := zConjBy gW zXi

@[expose] def zYiR (gW : List Int) : Array V2 := zConjBy gW zXiInv

@[expose] def zProdRows : List (Array V2) → Array V2
  | [] => idRows
  | r :: rs => mulRows r (zProdRows rs)

@[expose] def zS (i : Fin 4) : List (Fin 4) :=
  if i = 0 then [1] else if i = 1 then [2] else if i = 2 then [3] else [0, 1, 2, 3]

@[expose] def zRw (j : Nat) : Array V2 := wR (zcWord j)

@[expose] def zTs (T₀ : Array V2) (gW : List Int) (i : Fin 4) : List Nat :=
  zTabOf (zMs T₀ gW i) (zMs T₀ gW i)

@[expose] def chkZLight (T₀ : Array V2) (gW : List Int) : Bool :=
  eqRows (zConjBy gW T₀) (etaE 1) &&
    (List.finRange 4).all (fun i =>
      wfRows (zMs T₀ gW i) && eqRows (mulRows (zMs T₀ gW i) (zMs T₀ gW i)) idRows &&
        zTabOK (zMs T₀ gW i) (zMs T₀ gW i) (zTs T₀ gW i)) &&
    (List.finRange 4).all (fun i => (List.finRange 4).all fun j =>
      eqRows (mulRows (zMs T₀ gW i) (zMs T₀ gW j)) (mulRows (zMs T₀ gW j) (zMs T₀ gW i))) &&
    wfRows (zYR gW) &&
    (List.finRange 4).all fun i =>
      eqRows (mulRows (mulRows (zYR gW) (zMs T₀ gW i)) (zYiR gW))
        (zProdRows ((zS i).map (zMs T₀ gW)))

@[expose] def zTaus (T₀ : Array V2) (gW : List Int) : List Nat :=
  zcTaus (List.ofFn (zTs T₀ gW))

@[expose] def zEtaT : Array (Array V2) :=
  let T := uTab (locMats ()) (locInvs ())
  (Array.range 2048).map fun c => etaRows T 11 c

@[expose] def zIRowF (ms : Fin 4 → Array V2) (R : Array V2) (j : Nat) :
    List ((Nat × Nat) × Array V2) :=
  (List.range 2048).filterMap fun c =>
    if zRowsComm ms (mulRows zEtaT[c]! R) then some ((j, c), mulRows zEtaT[c]! R) else none

@[expose] def zIF (ms : Fin 4 → Array V2) (Rw : Nat → Array V2) (taus : List Nat) :
    List ((Nat × Nat) × Array V2) :=
  taus.flatMap fun j => zIRowF ms (Rw j) j

@[expose] def zMsArr (T₀ : Array V2) (gW : List Int) : Array (Array V2) :=
  #[zMs T₀ gW 0, zMs T₀ gW 1, zMs T₀ gW 2, zMs T₀ gW 3]

@[expose] def chkZHeavy (m k : Nat) (T₀ : Array V2) (gW : List Int) : Bool :=
  let msA := zMsArr T₀ gW
  let L := zIF (fun i : Fin 4 => msA[i.val]!) zRw (zTaus T₀ gW)
  L.all (fun p => eqRows (powRows p.2 (2 ^ m)) idRows) &&
    decide ((L.filter fun p => eqRows (mulRows p.2 (zYR gW)) (mulRows (zYR gW) p.2)).length ≤ k) &&
    decide (16 * k < L.length)

@[expose] def chkZ (m k : Nat) (T₀ : Array V2) (gW : List Int) : Bool :=
  chkZLight T₀ gW && chkZHeavy m k T₀ gW

end CFSG.QuasithinUnique.A5
