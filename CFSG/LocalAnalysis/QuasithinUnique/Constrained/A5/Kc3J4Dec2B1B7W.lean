module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Native
public import CFSG.Sporadic.J4.QTRankNative

public section

namespace CFSG.Sporadic.J4.QT2.B7

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def cntRowsT (K Ki M Mi : Array V2) (t : List Nat) : Option Nat :=
  if eqRows (mulRows K Ki) idRows && eqRows (mulRows M Mi) idRows then
    let Mq := mulRows (mulRows Ki M) K
    let Mqi := mulRows (mulRows Ki Mi) K
    if actTabOK Mq Mqi t then some ((List.range 2048).countP fun c => actT t c == c) else none
  else none

structure B7Wit where
  kw : List Int
  k : Nat
  t : List Nat

@[expose] def candOKW (Vs : Array (Array V2)) (qv : V2) (w : B7Wit) : Bool :=
  !(differs (frApply (frTable fiveRows) qv) qv) ||
    (let K := wR w.kw
     let Ki := invRows K
     let M := prodRows Vs w.k
     !(differs (frApply (frTable Ki) rootV) qv) && decide (1 ≤ w.k) && decide (w.k < 16) &&
       neId M && (match cntRowsT K Ki M M w.t with
         | some n => n != 128
         | none => false))

@[expose] def survP (T0 : Array V2) (g0w : List Int) (u : V2) : Prop :=
  fixedBy ((vRows T0).map frTable) (frApply (frTable (invRows (wR g0w))) u) = false ∨
    ∃ w : B7Wit, candOKW (vRows T0) (frApply (frTable (invRows (wR g0w))) u) w = true

@[expose] def B7Tree (r : V2) (P : List V2) : Prop :=
  P[0]? = some r ∧
    ∀ k, 0 < k → k < P.length → ∃ j < k, ∃ g < 3, P[k]! = frApply locTabs[g]! P[j]!

@[expose] def baseP (T0 : Array V2) : Prop :=
  ∀ k, 1 ≤ k → k < 16 → eqRows (prodRows (vRows T0) k) idRows = true ∨
    ∃ t, cntRowsT idRows idRows (prodRows (vRows T0) k) (prodRows (vRows T0) k) t = some 128

@[expose] def survOrb (T0 : Array V2) (g0w : List Int) (ℓ n : Nat) : Prop :=
  ∃ P : List V2, B7Tree (pathVec (repPaths.getD ℓ [])) P ∧ P.Nodup ∧ P.length = n ∧
    ∀ p ∈ P, p.wf = true ∧ survP T0 g0w p

end CFSG.Sporadic.J4.QT2.B7
