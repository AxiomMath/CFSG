module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Ord

open CFSG.KC.Loop

@[expose] noncomputable def rowOf3 (d N RM M i : Nat) : Nat :=
  Nat.add (Nat.land (Nat.shiftRight M (Nat.mul d i)) RM)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight M (Nat.add N (Nat.mul d i))) RM) d)

@[expose] noncomputable def decByte3 (d N RM M St b : Nat) : Nat :=
  nIf(andB (Nat.beq (Nat.land St (nat_lit 1)) (nat_lit 1)) (Nat.blt b (nat_lit 128)),
    nIf(Nat.beq (Nat.land (Nat.shiftRight St (nat_lit 1)) (nat_lit 1)) (nat_lit 1),
      nIf(ws b, St,
        (fun k R => nIf(Nat.blt k (Nat.mul d d),
            (fun j R' => nIf(Nat.beq (Nat.succ j) d,
                nIf(Nat.beq R' (rowOf3 d N RM M (Nat.div k d)),
                  Nat.add (nat_lit 3) (Nat.shiftLeft (Nat.succ k) (nat_lit 2)),
                  nat_lit 0),
                Nat.add (nat_lit 3) (Nat.add (Nat.shiftLeft (Nat.succ k) (nat_lit 2)) (Nat.shiftLeft R' (nat_lit 26)))))
              (Nat.mod k d)
              ((fun e j => Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land e (nat_lit 1)) j)
                  (Nat.shiftLeft (Nat.shiftRight e (nat_lit 1)) (Nat.add d j))))
                (ent (nat_lit 3) b) (Nat.mod k d)),
            St))
          (bitsN St (nat_lit 2) (nat_lit 24)) (Nat.shiftRight St (nat_lit 26))),
      nIf(Nat.beq b (nat_lit 10), Nat.lor St (nat_lit 2), St)),
    nat_lit 0)

@[expose] noncomputable def decRun3 (F : Nat → Nat) (lb len d N RM M : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun St => St)
    (fun leaf _ ih St => strictN (Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
        (fun q ih2 St => (fun idx => strictN
            (Bool.rec (motive := fun _ => Nat) St
              (decByte3 d N RM M St (Nat.land (Nat.shiftRight (F leaf) (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
              (Nat.blt idx len))
            ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q)))
        lb St) ih) Cs

@[expose] noncomputable def flagOK3 (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE Cm Ci : Nat) : Bool :=
  andB (vld Cm) (andB (vld Ci) (Nat.beq (mul Cm Ci) ONE))

@[expose] noncomputable def uniOK3 (RB : Nat → Nat) (mul : Nat → Nat → Nat) (N LO ONE UP Cm Ci PR lo hi : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (Bool.rec (motive := fun _ => Bool) true
    ((fun M => andB (Nat.beq (Nat.land (Nat.lor (Nat.land M LO) (Nat.shiftRight M N)) UP) (nat_lit 0))
        (Nat.beq (Nat.land M ONE) ONE))
      (mul (mul Cm (RB (at16 PR k))) Ci)) (Nat.ble lo k))) hi

end CFSG.KC.Ord

end
