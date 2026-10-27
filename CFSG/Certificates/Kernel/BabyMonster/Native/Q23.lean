module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

public section

namespace CFSG.KC.BM

@[expose] noncomputable def par32 (x : Nat) : Nat :=
  (fun a => (fun b => (fun c => (fun d => Nat.land (Nat.xor d (Nat.shiftRight d (nat_lit 1))) (nat_lit 1))
      (Nat.xor c (Nat.shiftRight c (nat_lit 2))))
    (Nat.xor b (Nat.shiftRight b (nat_lit 4))))
    (Nat.xor a (Nat.shiftRight a (nat_lit 8))))
  (Nat.xor (Nat.land x (nat_lit 65535)) (Nat.shiftRight x (nat_lit 16)))

@[expose] noncomputable def SPR31 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 682)) (nat_lit 1)) (nat_lit 2147483647)

@[expose] noncomputable def S32 : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 704)) (nat_lit 1)) (nat_lit 4294967295)

@[expose] noncomputable def xorFields (LO v : Nat) : Nat :=
  (fun x => (fun x1 => (fun x2 => (fun x3 => (fun x4 =>
      Nat.xor (Nat.land x4 (nat_lit 4294967295)) (Nat.shiftRight x4 (nat_lit 32)))
    (Nat.xor (Nat.land x3 (nat_lit 18446744073709551615)) (Nat.shiftRight x3 (nat_lit 64))))
    (Nat.xor (Nat.land x2 (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (nat_lit 1))) (Nat.shiftRight x2 (nat_lit 128))))
    (Nat.xor (Nat.land x1 (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))) (Nat.shiftRight x1 (nat_lit 256))))
    (Nat.xor (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 512)) (nat_lit 1))) (Nat.shiftRight x (nat_lit 512))))
  (Nat.land LO (Nat.mul (Nat.land (Nat.mul v SPR31) S32) (nat_lit 4294967295)))

@[expose] noncomputable def mulQ (LO a b : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.xor a b) (nat_lit 4194303))
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.shiftRight (Nat.xor a b) (nat_lit 22))
      (par32 (Nat.land (xorFields LO (Nat.land a (nat_lit 4194303))) b))) (nat_lit 1)) (nat_lit 22))

@[expose] noncomputable def autQ (LO A n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ out => out)
    (fun _ ih Ar v out => forceB (Bool.rec (motive := fun _ => Nat)
        (mulQ LO out (Nat.land Ar (nat_lit 4294967295))) out (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 0)))
      (fun o => ih (Nat.shiftRight Ar (nat_lit 32)) (Nat.shiftRight v (nat_lit 1)) o))
    (nat_lit 22) A (Nat.land n (nat_lit 4194303)) (Nat.land n (nat_lit 4194304))

@[expose] noncomputable def compAut (LO A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih Ar sh acc => forceB (Nat.lor acc (Nat.shiftLeft (autQ LO B (Nat.land Ar (nat_lit 4294967295))) sh))
      (fun a => ih (Nat.shiftRight Ar (nat_lit 32)) (Nat.add sh (nat_lit 32)) a))
    (nat_lit 22) A (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def ech22 (fromK : Bool) (Q k : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ st => st)
    (fun _ ih R i st => forceB
      ((fun r => Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) st (echStep r st) (Nat.ble k i))
          (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st (Nat.beq r (nat_lit 0)))
            (echStep r st) (Nat.blt i k))
          (notB fromK))
        (Nat.land R (nat_lit 4294967295)))
      (fun st' => ih (Nat.shiftRight R (nat_lit 32)) (Nat.succ i) st'))
    (nat_lit 22) Q (nat_lit 0) (Nat.shiftLeft (nat_lit 1) (nat_lit 40)))

@[expose] noncomputable def rank22 (M P Q k : Nat) : Bool :=
  andB (andB (wf32 (nat_lit 22) P) (Nat.beq (mm32 (nat_lit 22) P M) Q))
    (andB (ech22 false Q k) (ech22 true P k))

end CFSG.KC.BM

end
