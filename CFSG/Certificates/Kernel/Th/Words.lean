module

public import CFSG.Certificates.Kernel.Th.Mat

public section

namespace CFSG.KC.Th

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def wLet (w i : Nat) : Nat := Nat.land (Nat.shiftRight w (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def lInv (inv c : Nat) : Nat := wLet inv c

@[expose] noncomputable def strip (w n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun v m =>
      Bool.rec (Prod.mk (Nat.lor v (Nat.shiftLeft (wLet w i) (Nat.mul (nat_lit 8) m))) (Nat.succ m))
        (Prod.mk v m) (Nat.beq (wLet w i) (nat_lit 255))) acc) n

@[expose] noncomputable def rot (r n s : Nat) : Nat :=
  Nat.lor (Nat.shiftRight r (Nat.mul (nat_lit 8) s))
    (Nat.shiftLeft (Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) s)) (nat_lit 1)))
      (Nat.mul (nat_lit 8) (Nat.sub n s)))

@[expose] noncomputable def isRot (r n w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun s acc => orB acc (Nat.beq (rot r n s) w)) n

@[expose] noncomputable def isRelRot (r m w n : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v k => andB (Nat.beq k m) (isRot r m v)) (strip w n)

@[expose] noncomputable def freeRed (inv w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i stk => Bool.rec
      (Bool.rec (Nat.add (Nat.mul stk (nat_lit 256)) (Nat.succ (wLet w i)))
        (Nat.shiftRight stk (nat_lit 8))
        (andB (Nat.blt (nat_lit 0) stk)
          (Nat.beq (Nat.land stk (nat_lit 255)) (Nat.succ (lInv inv (wLet w i))))))
      stk (Nat.beq (wLet w i) (nat_lit 255))) n

@[expose] noncomputable def freeTriv (inv w n : Nat) : Bool := Nat.beq (freeRed inv w n) (nat_lit 0)

@[expose] noncomputable def chkWord (inv w n r m : Nat) : Bool := orB (freeTriv inv w n) (isRelRot r m w n)

@[expose] noncomputable def wInv (inv w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (lInv inv (wLet w i))
      (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub n i) (nat_lit 1))))) n

@[expose] noncomputable def wCat (a na b : Nat) : Nat := Nat.lor a (Nat.shiftLeft b (Nat.mul (nat_lit 8) na))

@[expose] noncomputable def chkPsiRel (inv V U sw ns pw np r m : Nat) : Bool :=
  andB (Nat.beq (Nat.add (Nat.add ns np) (nat_lit 2)) m)
    (isRot r m (wCat (wCat (wCat V (nat_lit 1) sw) (Nat.succ ns) U) (Nat.add ns (nat_lit 2)) (wInv inv pw np)))

end CFSG.KC.Th

end
