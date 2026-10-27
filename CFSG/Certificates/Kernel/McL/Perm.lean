module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.McL

open CFSG.KC

@[expose] noncomputable def pget (p i : Nat) : Nat :=
  Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 6) i)) (nat_lit 63)

@[expose] noncomputable def pmul (d p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (pget q (pget p i)) (Nat.mul (nat_lit 6) i))) d

@[expose] noncomputable def pid (d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul (nat_lit 6) i))) d

@[expose] noncomputable def pcyc (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.mod (Nat.succ i) n) (Nat.mul (nat_lit 6) i))) n

@[expose] noncomputable def inRange (d p : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (Nat.blt (pget p i) d)) d

@[expose] noncomputable def pairOK (d p q : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight p (Nat.mul (nat_lit 6) d)) (nat_lit 0))
    (andB (Nat.beq (Nat.shiftRight q (Nat.mul (nat_lit 6) d)) (nat_lit 0))
      (andB (inRange d p) (andB (inRange d q) (Nat.beq (pmul d p q) (pid d)))))

@[expose] noncomputable def evalW (G : Nat → Nat) (d W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pid d)
    (fun q acc => pmul d acc (G (wLet W q))) n

end CFSG.KC.McL

end
