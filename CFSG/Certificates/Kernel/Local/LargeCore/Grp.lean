module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.LL

open CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def fldW (r o w : Nat) : Nat :=
  Nat.land (Nat.shiftRight r o) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def getRec (blk : Nat → Nat) (RB i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 6)) (fun k =>
    fldW (blk k) (Nat.mul (Nat.land i (nat_lit 63)) RB) RB)

@[expose] noncomputable def recVal (blk : Nat → Nat) (RB vb i : Nat) : Nat :=
  fldW (getRec blk RB i) (nat_lit 0) vb

@[expose] noncomputable def pickL (l : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun k' _ => ih k') k) l j

@[expose] noncomputable def rmulL (mul : Nat → Nat → Nat) (gs : List Nat) (j x : Nat) : Nat :=
  mul x (pickL gs j)

@[expose] noncomputable def conjL (mul : Nat → Nat → Nat) (gs gis : List Nat) (j x : Nat) : Nat :=
  mul (mul (pickL gis j) x) (pickL gs j)

@[expose] noncomputable def ctRec (blk : Nat → Nat) (act : Nat → Nat → Nat)
    (vb db pb gb m n x0 i : Nat) : Bool :=
  (fun RB => letB (getRec blk RB i) (fun r =>
    letB (fldW r (nat_lit 0) vb) (fun x =>
    letB (fldW r vb db) (fun d =>
    letB (fldW r (Nat.add vb db) pb) (fun p =>
    letB (fldW r (Nat.add (Nat.add vb db) pb) gb) (fun g =>
    (fun T0 =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (recVal blk RB vb (Nat.sub i (nat_lit 1))) x),
    bAnd(bIf(Nat.beq d (nat_lit 0), Nat.beq x x0,
      bAnd(Nat.blt p n, bAnd(Nat.blt g m, letB (getRec blk RB p) (fun q =>
        bAnd(Nat.beq (Nat.succ (fldW q vb db)) d,
          Nat.beq (fldW q (Nat.add T0 (Nat.mul pb g)) pb) i))))),
    Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(ih,
      letB (fldW r (Nat.add T0 (Nat.mul pb j)) pb) (fun t =>
        bAnd(Nat.blt t n, Nat.beq (act j x) (recVal blk RB vb t))))) m)))
    (Nat.add (Nat.add (Nat.add vb db) pb) gb)))))))
  (Nat.add (Nat.add (Nat.add (Nat.add vb db) pb) gb) (Nat.mul m pb))

@[expose] noncomputable def ctRange (blk : Nat → Nat) (act : Nat → Nat → Nat)
    (vb db pb gb m n x0 lo c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => ctRec blk act vb db pb gb m n x0 (Nat.add lo j))

@[expose] noncomputable def memAt (blk : Nat → Nat) (RB vb n k x : Nat) : Bool :=
  bAnd(Nat.blt k n, Nat.beq (recVal blk RB vb k) x)

@[expose] noncomputable def wordR (mul : Nat → Nat → Nat) (gen : Nat → Nat) (ONE : Nat)
    (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => strictN (mul acc (gen a)) ih) w ONE

@[expose] noncomputable def powNB (mul : Nat → Nat → Nat) (ONE x e nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (mul acc acc) (fun a2 =>
      strictN (nIf(Nat.blt (nat_lit 0) (Nat.land e (Nat.shiftLeft (nat_lit 1) j)),
        mul a2 x, a2)) ih)) nb ONE

@[expose] noncomputable def primeOrd (mul : Nat → Nat → Nat) (ONE x q nb : Nat) : Bool :=
  bAnd(Nat.beq (powNB mul ONE x q nb) ONE, bIf(Nat.beq x ONE, false, true))

@[expose] noncomputable def twoPowOrd (mul : Nat → Nat → Nat) (ONE x k : Nat) : Bool :=
  (fun y => bAnd(Nat.beq (mul y y) ONE, bIf(Nat.beq y ONE, false, true)))
    (Nat.rec (motive := fun _ => Nat) x (fun _ acc => strictN acc (fun a => mul a a)) (Nat.sub k (nat_lit 1)))

@[expose] noncomputable def commM (mul : Nat → Nat → Nat) (x y : Nat) : Bool :=
  Nat.beq (mul x y) (mul y x)

end CFSG.KC.LL

end
