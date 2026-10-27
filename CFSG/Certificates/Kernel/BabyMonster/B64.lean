module

public import CFSG.Certificates.Kernel.BabyMonster.F2

public section

namespace CFSG.KC.BM.B64

open CFSG.KC.BM

@[expose] noncomputable def inR (lo hi c : Nat) : Bool := andB (Nat.ble lo c) (Nat.ble c hi)

@[expose] noncomputable def b64v (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 63) (Nat.beq c (nat_lit 47)))
          (nat_lit 62) (Nat.beq c (nat_lit 43)))
        (Nat.add c (nat_lit 4)) (inR (nat_lit 48) (nat_lit 57) c))
      (Nat.sub c (nat_lit 71)) (inR (nat_lit 97) (nat_lit 122) c))
    (Nat.sub c (nat_lit 65)) (inR (nat_lit 65) (nat_lit 90) c)

@[expose] noncomputable def chAt (N i : Nat) : Nat :=
  Nat.land (Nat.shiftRight N (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def quadV (N q : Nat) : Nat :=
  (fun i => Nat.lor (Nat.lor (Nat.shiftLeft (b64v (chAt N i)) (nat_lit 18))
      (Nat.shiftLeft (b64v (chAt N (Nat.add i (nat_lit 1)))) (nat_lit 12)))
    (Nat.lor (Nat.shiftLeft (b64v (chAt N (Nat.add i (nat_lit 2)))) (nat_lit 6))
      (b64v (chAt N (Nat.add i (nat_lit 3))))))
  (Nat.mul (nat_lit 4) q)

@[expose] noncomputable def tripleOf (v : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight v (nat_lit 16)) (nat_lit 255))
    (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 8)) (nat_lit 255)) (nat_lit 8))
      (Nat.shiftLeft (Nat.land v (nat_lit 255)) (nat_lit 16)))

@[expose] noncomputable def segDec (N q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => forceB ih (fun a =>
      Nat.lor a (Nat.shiftLeft (tripleOf (quadV N k)) (Nat.mul (nat_lit 24) k)))) q

@[expose] noncomputable def low551 : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4408)) (nat_lit 1)

@[expose] noncomputable def lastByte (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (nat_lit 4408)) (nat_lit 255)

@[expose] noncomputable def hdrNat : Nat :=
  Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (nat_lit 4370) (nat_lit 32))
    (Nat.lor (Nat.shiftLeft (nat_lit 1) (nat_lit 64)) (Nat.shiftLeft (nat_lit 69) (nat_lit 96))))

@[expose] noncomputable def hdrOK (p : Nat × Nat) : Bool :=
  andB (Nat.beq p.2 (nat_lit 20)) (Nat.beq (segDec p.1 (nat_lit 5)) hdrNat)

@[expose] noncomputable def segWant (R : Nat → Nat) (j : Nat) : Nat :=
  Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i _ => lastByte (R i)) j)
    (Nat.shiftLeft (Nat.land (R j) low551) (nat_lit 8))

@[expose] noncomputable def segOK (R : Nat → Nat) (j : Nat) (p : Nat × Nat) : Bool :=
  andB (Nat.beq p.2 (nat_lit 736)) (Nat.beq (segDec p.1 (nat_lit 184)) (segWant R j))

@[expose] noncomputable def lastOK (R : Nat → Nat) (p : Nat × Nat) : Bool :=
  andB (Nat.beq p.2 (nat_lit 2))
    (Nat.beq (Nat.land (segDec p.1 (nat_lit 1)) (nat_lit 255)) (lastByte (R (nat_lit 4369))))

@[expose] noncomputable def rangeOK (L : List (Nat × Nat)) (j c : Nat) (R : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c (nat_lit 0))
    (fun p _ ih j c => Bool.rec (motive := fun _ => Bool)
      (andB (segOK R j p) (ih (Nat.succ j) (Nat.sub c (nat_lit 1)))) true (Nat.beq c (nat_lit 0)))
    L j c

@[expose] noncomputable def dropP (L : List (Nat × Nat)) (k : Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun x xs ih k => Nat.rec (motive := fun _ => List (Nat × Nat)) (List.cons x xs)
      (fun j _ => ih j) k) L k

@[expose] noncomputable def getP (L : List (Nat × Nat)) (k : Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (fun p _ _ => p) (dropP L k)

@[expose] noncomputable def lenP (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

end CFSG.KC.BM.B64

end
