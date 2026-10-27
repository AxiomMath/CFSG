module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound.Spin

open CFSG.Sporadic.SmallF2.Native

@[expose] def cact (d : Nat) (X : Array Nat) (v : Nat) : Nat := vecMulN d (transposeRows d X) v

@[expose] def validR (d : Nat) (R : Array Nat) : Bool := R.size == d && R.all (· < 2 ^ d)

@[expose] def addRows (d : Nat) (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => X[i.val]?.getD 0 ^^^ Y[i.val]?.getD 0

@[expose] def zeroRows (d : Nat) : Array Nat := Array.replicate d 0

@[expose] def letterRows (d : Nat) (rs is : List (Array Nat)) (j : Int) : Array Nat :=
  if 0 < j then rs.getD (j.toNat - 1) (idRows d) else is.getD ((-j).toNat - 1) (idRows d)

@[expose] def wordRows (d : Nat) (rs is : List (Array Nat)) (w : List Int) : Array Nat :=
  w.foldl (fun acc j => mulRows d acc (letterRows d rs is j)) (idRows d)

structure SpinData where
  d : Nat
  rs : List (Array Nat)
  is : List (Array Nat)
  v0 : Nat
  bw : List (List Int)
  C : Array Nat
  sel : List (Nat × Nat × Nat)
  lam : Array Nat
  wcols : List Nat
  pcoords : List Nat

@[expose] def annW (d : Nat) (rs : List (Array Nat)) (C : Array Nat) (A : List (Array Nat))
    (b : List Nat) (j i : Nat) : Array Nat :=
  let s := rs.getD j (idRows d)
  let c := vecMulN d C (cact d s (b.getD i 0))
  addRows d
    ((List.range d).foldl (fun acc k =>
      if c.testBit k then addRows d acc (A.getD k (zeroRows d)) else acc) (zeroRows d))
    (mulRows d s (A.getD i (zeroRows d)))

@[expose] def eselW (d : Nat) (rs : List (Array Nat)) (C : Array Nat) (A : List (Array Nat))
    (b : List Nat) (sel : List (Nat × Nat × Nat)) : Array Nat :=
  (sel.map fun t => (annW d rs C A b t.1 t.2.1)[t.2.2]?.getD 0).toArray

@[expose] def mxW (d : Nat) (C : Array Nat) (A : List (Array Nat)) (w : Nat) : Array Nat :=
  transposeRows d (mulRows d C ((A.map fun X => cact d X w).toArray))

namespace SpinData

@[expose] def A (D : SpinData) : List (Array Nat) := D.bw.map (wordRows D.d D.rs D.is)

@[expose] def b (D : SpinData) : List Nat := D.A.map fun X => cact D.d X D.v0

@[expose] def wcolsArr (D : SpinData) : Array Nat :=
  Array.ofFn (n := D.d) fun k => D.wcols.getD k.val 0

@[expose] def Wp (D : SpinData) : Array Nat := transposeRows D.d D.wcolsArr

@[expose] def Pp (D : SpinData) : Array Nat :=
  Array.ofFn (n := D.d) fun k => if k.val < D.wcols.length then 1 <<< D.pcoords.getD k.val 0 else 0

@[expose] def wx (D : SpinData) (x : Nat) : Nat := vecMulN D.d D.wcolsArr x

@[expose] def esel (D : SpinData) : Array Nat := eselW D.d D.rs D.C D.A D.b D.sel

@[expose] def mx (D : SpinData) (x : Nat) : Array Nat := mxW D.d D.C D.A (D.wx x)

end SpinData

@[expose] def spinOK (D : SpinData) : Bool :=
  let d := D.d
  let A := D.A
  let b := D.b
  let At := A.map (transposeRows d)
  let esel := eselW d D.rs D.C A b D.sel
  decide (D.rs.length = D.is.length) &&
  (List.range D.rs.length).all (fun j =>
    mulRows d (D.rs.getD j #[]) (D.is.getD j #[]) == idRows d) &&
  decide (D.bw.length = d) && decide (b.length = d) && decide (D.C.size = d) &&
  mulRows d D.C b.toArray == idRows d &&
  decide (D.sel.length = d) &&
  D.sel.all (fun t => cact d (annW d D.rs D.C A b t.1 t.2.1) D.v0 == 0) &&
  decide (D.wcols.length ≤ d) &&
  addRows d (idRows d) (mulRows d D.Wp D.Pp) == mulRows d D.lam esel &&
  (List.range (2 ^ D.wcols.length)).all (fun x =>
    let w := D.wx x
    let Mt := transposeRows d (mxW d D.C A w)
    (List.range d).all (fun i => vecMulN d Mt (b.getD i 0) == vecMulN d (At.getD i #[]) w))

end CFSG.EvenSporadicStandard.Induction.AutBound.Spin
