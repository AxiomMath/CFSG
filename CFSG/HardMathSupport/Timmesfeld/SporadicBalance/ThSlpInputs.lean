module

public import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public import Certificates.Data.CFSGNative.SectionRank.Elem3
public meta import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public meta import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native

set_option compiler.extract_closed false

@[expose] def opRows (R : Array (Array V4)) : Op → Array (Array V4)
  | .mul i j k => R.setIfInBounds k (mulRows R[i]! R[j]!)
  | .pow e i k => R.setIfInBounds k (powRowsN R[i]! e)

@[expose] def initRows (A B : Array V4) (n : Nat) : Array (Array V4) :=
  Array.ofFn (n := n) fun r => if r.val = 0 then A else if r.val = 1 then B else idRows

@[expose] def slpRows (A B : Array V4) (n : Nat) (prog : List Op) : Array (Array V4) :=
  prog.foldl opRows (initRows A B n)

@[expose] def wordRowsL (gs : Array (Array V4)) (w : List Nat) : Array V4 :=
  w.foldl (fun acc r => mulRows acc gs[r]!) idRows

@[expose] def rowAt (X : Array V4) (k : Nat) : V4 := X[k]?.getD V4.zero

@[expose] def rowsDiffer (X Y : Array V4) : Bool :=
  (List.range 248).any fun k => (List.range 248).any fun c =>
    (rowAt X k).testBit c != (rowAt Y k).testBit c

@[expose] def pairOK (X Y : Array V4) (p : Nat) : Bool :=
  eqRows (powRowsN X p) idRows && eqRows (powRowsN Y p) idRows &&
    eqRows (mulRows X Y) (mulRows Y X) && rowsDiffer X idRows &&
    (List.range p).all fun k => rowsDiffer Y (powRowsN X k)

@[expose] def conjOK (regs : Array (Array V4)) (X Y Z : Array V4) (p : Nat)
    (W : Array (List Nat)) : Bool :=
  (List.range p).all fun a => (List.range p).all fun b => a + b == 0 ||
    ((W[p * a + b]!).all (fun r => decide (r < regs.size)) &&
      let M := wordRowsL regs W[p * a + b]!
      eqRows (mulRows M (mulRows (powRowsN X a) (powRowsN Y b))) (mulRows Z M))

@[expose] def cubeRows (X Y C : Array V4) (p row : Nat) : Array (Array (Array V4)) :=
  Array.ofFn (n := p) fun i => Array.ofFn (n := p) fun j => Array.ofFn (n := p) fun k =>
    rowAt (mulRows (mulRows (powRowsN X i.val) (powRowsN Y j.val)) (powRowsN C k.val)) row

@[expose] def cubeOK (X Y C : Array V4) (p row : Nat) : Bool :=
  let T := cubeRows X Y C p row
  eqRows (powRowsN X p) idRows && eqRows (powRowsN Y p) idRows &&
    eqRows (mulRows C X) (mulRows X C) && eqRows (mulRows C Y) (mulRows Y C) &&
    (List.range p).all fun i => (List.range p).all fun j => (List.range p).all fun k =>
      (T[i]![j]![k]!).wf && (List.range p).all fun i' => (List.range p).all fun j' =>
        (List.range p).all fun k' =>
          (i == i' && j == j' && k == k') || !(T[i]![j]![k]!).beq (T[i']![j']![k']!)

@[expose] def conj3OK (regs : Array (Array V4)) (X Y C : Array V4) (p : Nat)
    (W : Array (List Nat)) : Bool :=
  (List.range p).all fun i => (List.range p).all fun j => (List.range p).all fun k =>
    i + j + k == 0 ||
      ((W[p * p * i + p * j + k]!).all (fun r => decide (r < regs.size)) &&
        let M := wordRowsL regs W[p * p * i + p * j + k]!
        eqRows (mulRows M (mulRows (mulRows (powRowsN X i) (powRowsN Y j)) (powRowsN C k)))
          (mulRows C M))

@[expose] def stripOK (n : Nat) (zT gpl alphaT betaInvT : Table) (q0 : Table × Table × Table)
    (xT yiT z0T z1T : Table) (p0 : Nat) : Bool :=
  let r := stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0
  let qw := smallBFS r.2[2]! 60 z0T z1T
  decide (p0 < n) && decide (r.1 < q0Size) && r.2[0]! == 0 && r.2[1]! == 1 &&
    treeOK n q1Size r.2[2]! qw.1 qw.2 (findPt qw.1) z0T z1T

@[expose] def centCheckAuto (Z : Array V4) (bound c lo k : Nat) : Bool :=
  let st := thBFS ()
  let n := st.count
  let alphaT := tblOfBytes n st.alpha
  let betaT := tblOfBytes n st.beta
  let gpl := tblOfBytes n st.par
  let betaInvT := invT n betaT
  let X := xRows ()
  let Y := yRows ()
  let Z0 := z0Rows ()
  let Z1 := z1Rows ()
  let zT := matTable st (frTable (transposeRows Z)) n c
  let xT := matTable st (frTable (transposeRows X)) n c
  let yT := matTable st (frTable (transposeRows Y)) n c
  let yiT := invT n yT
  let z0T := matTable st (frTable (transposeRows Z0)) n c
  let z1T := matTable st (frTable (transposeRows Z1)) n c
  let q0 := localBFS n 1 xT yT
  let p0 := lo + (((List.range k).find? fun i =>
    stripOK n zT gpl alphaT betaInvT q0 xT yiT z0T z1T (lo + i)).getD 0)
  let r := stripZ zT gpl alphaT betaInvT q0.2.1 q0.2.2 xT yiT p0
  let qw := smallBFS r.2[2]! 60 z0T z1T
  centChecks st n p0 bound c Z X Y Z0 Z1 zT xT yT yiT z0T z1T alphaT betaInvT gpl q0 qw

structure CoreList where
  n : Nat
  m : Nat
  row : Nat
  words : Array (List Nat)
  inv : Array Nat
  wit : Array (List Nat)

@[expose] def witProd (E : Array (Array V4)) (inv : Array Nat) (i : Nat) (l : List Nat) :
    Array V4 :=
  l.foldl (fun P j => mulRows P (mulRows (mulRows E[j]! E[i]!) E[inv[j]!]!)) E[i]!

@[expose] def coreListOK (regs : Array (Array V4)) (Z : Array V4) (D : CoreList) : Bool :=
  let E := D.words.map (wordRowsL regs)
  decide (D.words.size = D.n) && decide (D.inv.size = D.n) && decide (D.wit.size = D.n) &&
    D.words.all (fun w => w.all fun r => decide (r < regs.size)) &&
    D.wit.all (fun l => l.all fun j => decide (j < D.n)) &&
    D.inv.all (fun j => decide (j < D.n)) &&
    E.all (fun X => eqRows (mulRows X Z) (mulRows Z X)) &&
    E.all (fun X => (rowAt X D.row).wf) &&
    (List.range D.n).all (fun i => (List.range i).all fun j =>
      !(rowAt E[i]! D.row).beq (rowAt E[j]! D.row)) &&
    (List.range D.n).all (fun i => eqRows (mulRows E[i]! E[D.inv[i]!]!) idRows) &&
    (List.range D.n).all (fun i => eqRows E[i]! idRows ||
      rowsDiffer (powRowsN (witProd E D.inv i D.wit[i]!) D.m) idRows)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
