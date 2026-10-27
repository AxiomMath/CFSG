module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Ord

open CFSG.KC.Loop

@[expose] noncomputable def rhsSeg (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PW p pb x lo m acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) acc (fun t a => strictN a (fun a' => (fun k => (fun e => Bool.rec (motive := fun _ => Nat)
      (mul a' (RB (at16 PW (Nat.sub (Nat.add (Nat.mul k p) e) (nat_lit 1))))) a' (Nat.beq e (nat_lit 0)))
    (bitsN x (Nat.mul pb k) pb)) (Nat.add lo t))) m

@[expose] noncomputable def pcSegOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PW n p pb x lo m Ain Aout : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.beq (rhsSeg RB mul PW p pb x lo m Ain) Aout)

@[expose] noncomputable def pcRelLitOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PR PW n p pb i j x R : Nat) : Bool :=
  andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (Nat.mul pb k) pb) p)
        (Nat.beq (bitsN x (Nat.mul pb k) pb) (nat_lit 0)) (Nat.ble k i))) n)
    (Bool.rec (motive := fun _ => Bool)
      (Nat.beq (mul (RB (at16 PR j)) (RB (at16 PR i))) (mul (RB (at16 PR i)) R))
      (Nat.beq (RB (at16 PW (Nat.sub (Nat.add (Nat.mul i p) p) (nat_lit 1)))) R)
      (Nat.beq i j))

@[expose] noncomputable def pcStepLit (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PR PW n p pb x R S : Nat) : Nat :=
  (fun i j => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) (Nat.add S (nat_lit 256))
        (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1) n)
          (Nat.add (nat_lit 1) (Nat.add (Nat.succ i) (Nat.shiftLeft (Nat.succ i) (nat_lit 8)))) (Nat.blt (Nat.succ i) n))
        (Nat.beq (Nat.succ j) n))
      (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt i n) (andB (Nat.blt j n)
        (pcRelLitOK RB mul PR PW n p pb i j x R)))))
    (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 255)) (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 8))

@[expose] noncomputable def invRangeOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (L ONE lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) L) (Nat.rec (motive := fun _ => Bool) true (fun t ih => andB ih
    ((fun g => andB (vld (RB (Nat.add (Nat.succ L) g)))
        (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ L) g))) ONE)) (Nat.add lo t))) m)

@[expose] noncomputable def pwEntryOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (PR PW n p nreg k e : Nat) : Bool :=
  andB (Nat.blt k n) (andB (Nat.blt e p) (Bool.rec (motive := fun _ => Bool)
    (andB (regBelow (at16 PW (Nat.add (Nat.mul k p) e)) nreg)
      (Nat.beq (RB (at16 PW (Nat.add (Nat.mul k p) e)))
        (mul (RB (at16 PW (Nat.sub (Nat.add (Nat.mul k p) e) (nat_lit 1)))) (RB (at16 PR k)))))
    (Nat.beq (at16 PW (Nat.mul k p)) (at16 PR k))
    (Nat.beq e (nat_lit 0))))

@[expose] noncomputable def powSeg (mul : Nat → Nat → Nat) (ONE M e lo m acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) acc
    (fun t ih => strictN ih (fun a => (fun i =>
      (fun sq => Bool.rec (motive := fun _ => Nat) sq
          (Bool.rec (motive := fun _ => Nat) (mul sq M) M (Nat.beq sq ONE))
          (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1)) (nat_lit 1)))
        (Bool.rec (motive := fun _ => Nat) (mul a a) a (Nat.beq a ONE))) (Nat.add lo t))) m

@[expose] noncomputable def powSegOK (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE r q lo m Ain Aout : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) (nat_lit 16)) (Nat.beq (powSeg mul ONE (RB r) q lo m Ain) Aout)

@[expose] noncomputable def primeNZ (RB : Nat → Nat) (ONE nreg r q : Nat) : Bool :=
  andB (regBelow r nreg) (andB (Nat.blt q (nat_lit 65536)) (notB (Nat.beq (RB r) ONE)))

end CFSG.KC.Ord

end
