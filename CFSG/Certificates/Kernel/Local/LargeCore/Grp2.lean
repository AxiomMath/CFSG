module

public import CFSG.Certificates.Kernel.Local.LargeCore.Grp

public section

namespace CFSG.KC.LL

open CFSG.KC.Loop

@[expose] noncomputable def ctlRec (blk : Nat → Nat) (act : Nat → Nat → Nat)
    (vb lb db pb gb m n REP i : Nat) : Bool :=
  (fun RB T0 => letB (getRec blk RB i) (fun r =>
    letB (fldW r (nat_lit 0) vb) (fun x =>
    letB (fldW r vb lb) (fun L =>
    letB (fldW r (Nat.add vb lb) db) (fun d =>
    letB (fldW r (Nat.add (Nat.add vb lb) db) pb) (fun p =>
    letB (fldW r (Nat.add (Nat.add (Nat.add vb lb) db) pb) gb) (fun g =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (recVal blk RB vb (Nat.sub i (nat_lit 1))) x),
    bAnd(bIf(Nat.beq d (nat_lit 0), Nat.beq (fldW REP (Nat.mul pb L) pb) i,
      bAnd(Nat.blt p n, bAnd(Nat.blt g m, letB (getRec blk RB p) (fun q =>
        bAnd(Nat.beq (Nat.succ (fldW q (Nat.add vb lb) db)) d,
          bAnd(Nat.beq (fldW q vb lb) L, Nat.beq (fldW q (Nat.add T0 (Nat.mul pb g)) pb) i)))))),
    Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(ih,
      letB (fldW r (Nat.add T0 (Nat.mul pb j)) pb) (fun t =>
        bAnd(Nat.blt t n, letB (getRec blk RB t) (fun s =>
          bAnd(Nat.beq (fldW s vb lb) L, Nat.beq (act j x) (fldW s (nat_lit 0) vb))))))) m)))))))))
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add vb lb) db) pb) gb) (Nat.mul m pb))
  (Nat.add (Nat.add (Nat.add (Nat.add vb lb) db) pb) gb)

@[expose] noncomputable def ctlRange (blk : Nat → Nat) (act : Nat → Nat → Nat)
    (vb lb db pb gb m n REP lo c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => ctlRec blk act vb lb db pb gb m n REP (Nat.add lo j))

@[expose] noncomputable def labCount (blk : Nat → Nat) (RB vb lb L lo c : Nat) : Nat :=
  sumBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => nIf(Nat.beq (fldW (getRec blk RB (Nat.add lo j)) vb lb) L, nat_lit 1, nat_lit 0))

@[expose] noncomputable def countIf (blk : Nat → Nat) (RB vb : Nat) (pr : Nat → Bool) (lo c : Nat) : Nat :=
  sumBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => nIf(pr (recVal blk RB vb (Nat.add lo j)), nat_lit 1, nat_lit 0))

@[expose] noncomputable def notInSorted (blk : Nat → Nat) (RB vb n x j : Nat) : Bool :=
  bIf(Nat.beq j n, Nat.blt x (recVal blk RB vb (nat_lit 0)),
    bIf(Nat.beq j (Nat.succ n), Nat.blt (recVal blk RB vb (Nat.sub n (nat_lit 1))) x,
      bAnd(Nat.blt (Nat.succ j) n, bAnd(Nat.blt (recVal blk RB vb j) x,
        Nat.blt x (recVal blk RB vb (Nat.succ j))))))

@[expose] noncomputable def pAt (w p i : Nat) : Nat := fldW p (Nat.mul w i) w

@[expose] noncomputable def pMul (n w p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (pAt w p (pAt w q i)) (Nat.mul w i))) n

@[expose] noncomputable def pFromL (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih k => Nat.lor (Nat.shiftLeft e (Nat.mul w k)) (ih (Nat.succ k))) l (nat_lit 0)

@[expose] noncomputable def isPerm (n w p : Nat) : Bool :=
  (fun r => bAnd(Nat.blt (nat_lit 0) r, Nat.beq r (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ n)) (nat_lit 1))))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 1)
      (fun i acc => (fun e => nIf(bAnd(Nat.blt (nat_lit 0) acc, bAnd(Nat.blt e n, Nat.beq (Nat.land acc (Nat.shiftLeft (nat_lit 2) e)) (nat_lit 0))),
          Nat.lor acc (Nat.shiftLeft (nat_lit 2) e), nat_lit 0)) (pAt w p i)) n)

@[expose] noncomputable def lpermL (n w : Nat) (gs : List Nat) (j x : Nat) : Nat := pMul n w (pickL gs j) x

end CFSG.KC.LL

end
