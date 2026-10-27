module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.MonsterConv.Orb

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def getRec (blk : Nat → Nat) (RB i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 6)) (fun k =>
    Nat.land (Nat.shiftRight (blk k) (Nat.mul (Nat.land i (nat_lit 63)) RB))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) RB) (nat_lit 1)))

@[expose] noncomputable def fldW (r o w : Nat) : Nat :=
  Nat.land (Nat.shiftRight r o) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def recOKw (blk : Nat → Nat) (act : Nat → Nat → Nat) (vb pb gb db n x0 i : Nat) : Bool :=
  (fun RB => letB (getRec blk RB i) (fun r =>
    andB
      (Bool.rec (motive := fun _ => Bool)
        (Nat.blt (fldW (getRec blk RB (Nat.sub i (nat_lit 1))) (nat_lit 0) vb) (fldW r (nat_lit 0) vb))
        true (Nat.beq i (nat_lit 0)))
      ((fun x p g d => Bool.rec (motive := fun _ => Bool)
          (andB (Nat.blt p n) (letB (getRec blk RB p) (fun q =>
            andB (Nat.beq (Nat.succ (fldW q (Nat.add (Nat.add vb pb) gb) db)) d)
              (Nat.beq (act g (fldW q (nat_lit 0) vb)) x))))
          (Nat.beq x x0)
          (Nat.beq d (nat_lit 0)))
        (fldW r (nat_lit 0) vb) (fldW r vb pb) (fldW r (Nat.add vb pb) gb) (fldW r (Nat.add (Nat.add vb pb) gb) db))))
    (Nat.add (Nat.add vb pb) (Nat.add gb db))

@[expose] noncomputable def recOK (blk : Nat → Nat) (act : Nat → Nat → Nat) (F n x0 i : Nat) : Bool :=
  recOKw blk act (Nat.land F (nat_lit 255)) (Nat.land (Nat.shiftRight F (nat_lit 8)) (nat_lit 255))
    (Nat.land (Nat.shiftRight F (nat_lit 16)) (nat_lit 255)) (Nat.shiftRight F (nat_lit 24)) n x0 i

@[expose] noncomputable def orbRange16 (blk : Nat → Nat) (act : Nat → Nat → Nat) (F n x0 lo c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => recOKw blk act (fldW F (nat_lit 0) (nat_lit 16)) (fldW F (nat_lit 16) (nat_lit 16))
      (fldW F (nat_lit 32) (nat_lit 16)) (fldW F (nat_lit 48) (nat_lit 16)) n x0 (Nat.add lo j))

@[expose] noncomputable def orbRange (blk : Nat → Nat) (act : Nat → Nat → Nat) (F n x0 lo c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => recOK blk act F n x0 (Nat.add lo j))

@[expose] noncomputable def linApply (TB w nb x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.xor acc
      (fldW TB (Nat.mul w (Nat.add (Nat.mul (nat_lit 256) c) (fldW x (Nat.mul (nat_lit 8) c) (nat_lit 8)))) w))
    nb

@[expose] noncomputable def linTables (col : Nat → Nat) (w nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun b T => strictN T (fun T' => Nat.lor T'
          (Nat.shiftLeft
            (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
              (fun t U => Nat.lor U (Nat.shiftLeft
                (Nat.xor (fldW T' (Nat.mul w t) w) (col (Nat.add (Nat.mul (nat_lit 8) c) b)))
                (Nat.mul w t)))
              (Nat.shiftLeft (nat_lit 1) b))
            (Nat.mul w (Nat.shiftLeft (nat_lit 1) b)))))
        (nat_lit 8))
      (Nat.mul w (Nat.mul (nat_lit 256) c))))
    nb

@[expose] noncomputable def tupAct (RAW rec b m g x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 12) b))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft
        (fldW RAW (Nat.add (Nat.mul rec (fldW x (Nat.mul (nat_lit 12) i) (nat_lit 12))) (Nat.mul (nat_lit 32) g)) (nat_lit 32))
        (Nat.mul (nat_lit 12) i))) b)
    (Nat.blt g m)

@[expose] noncomputable def linAct (TBs : Nat → Nat) (w nb g x : Nat) : Nat := linApply (TBs g) w nb x

@[expose] noncomputable def tablesOK (TB COLS w nb : Nat) : Bool :=
  Nat.beq TB (linTables (fun i => fldW COLS (Nat.mul w i) w) w nb)

end CFSG.KC.MonsterConv.Orb

end
