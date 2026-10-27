module

public import CFSG.Certificates.Kernel.J4.M12

public section

namespace CFSG.KJ4

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

@[expose] noncomputable def chkPsiRel (inv T sw ns pw np r m : Nat) : Bool :=
  andB (Nat.beq (Nat.add (Nat.add ns np) (nat_lit 2)) m)
    (isRot r m (wCat (wCat (wCat T (nat_lit 1) sw) (Nat.succ ns) T) (Nat.add ns (nat_lit 2)) (wInv inv pw np)))

@[expose] noncomputable def substZ (w n zw zwi m : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun v k =>
      Bool.rec
        (Bool.rec (Prod.mk (wCat v k (wLet w i)) (Nat.succ k))
          (Prod.mk (wCat v k zwi) (Nat.add k m)) (Nat.beq (wLet w i) (nat_lit 6)))
        (Prod.mk (wCat v k zw) (Nat.add k m)) (Nat.beq (wLet w i) (nat_lit 5))) acc) n

@[expose] noncomputable def chkSubst (w n zw zwi m u k : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v l => andB (Nat.beq l k) (Nat.beq v u)) (substZ w n zw zwi m)

@[expose] noncomputable def chkSubstRed (inv w n zw zwi m u k : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v l => Nat.beq (freeRed inv v l) (freeRed inv u k))
    (substZ w n zw zwi m)

@[expose] noncomputable def letMat (LET c : Nat) : Nat :=
  Nat.land (Nat.shiftRight LET (Nat.mul (nat_lit 144) c)) (nat_lit 22300745198530623141535718272648361505980415)

@[expose] noncomputable def evalW (LET w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ident12 (fun i acc => mul12 acc (letMat LET (wLet w i))) n

@[expose] noncomputable def chkEval (LET w n M : Nat) : Bool := Nat.beq (evalW LET w n) M

end CFSG.KJ4

end
