module

public section

namespace CFSG.KC

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def rget (B off : Nat) : Nat :=
  Nat.land (Nat.shiftRight B off) (nat_lit 72057594037927935)

@[expose] noncomputable def fx (R : Nat) : Nat := Nat.land R (nat_lit 1048575)
@[expose] noncomputable def fc (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 20)) (nat_lit 255)
@[expose] noncomputable def fy (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 28)) (nat_lit 1048575)
@[expose] noncomputable def fic (R : Nat) : Nat := Nat.shiftRight R (nat_lit 48)
@[expose] noncomputable def fxc (R : Nat) : Nat := Nat.land R (nat_lit 268435455)
@[expose] noncomputable def fyic (R : Nat) : Nat := Nat.shiftRight R (nat_lit 28)

@[expose] noncomputable def inv16 (INV c : Nat) : Nat :=
  Nat.land (Nat.shiftRight INV (Nat.shiftLeft c (nat_lit 4))) (nat_lit 65535)

@[expose] noncomputable def recOK (INV nC R : Nat) : Bool :=
  andB (Nat.blt (fx R) nC) (andB (Nat.blt (fy R) nC) (Nat.beq (fic R) (inv16 INV (fc R))))

@[expose] noncomputable def wStart (s W : Nat) : Nat := Nat.lor s (Nat.shiftLeft W (nat_lit 20))

@[expose] noncomputable def sF (R st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (Nat.lor (fy R) (Nat.shiftLeft (Nat.shiftRight st (nat_lit 28)) (nat_lit 20)))
    (Nat.beq (Nat.land st (nat_lit 268435455)) (fxc R))

@[expose] noncomputable def sB (R st : Nat) : Nat :=
  Bool.rec (nat_lit 0) (Nat.lor (fx R) (Nat.shiftLeft (Nat.shiftRight st (nat_lit 28)) (nat_lit 20)))
    (Nat.beq (Nat.land st (nat_lit 268435455)) (fyic R))

@[expose] noncomputable def fWalk (INV nC R E st : Nat) : Bool := andB (recOK INV nC R) (Nat.beq st E)

@[expose] noncomputable def fTree (INV nC L R k : Nat) : Bool :=
  andB (recOK INV nC R) (andB (Nat.beq (fy R) k) (andB (Nat.blt (fx R) k) (Nat.blt (fc R) L)))

@[expose] noncomputable def aliveAt (LV k y : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight y (nat_lit 12)) k)
    (Nat.blt (nat_lit 0) (Nat.land LV (Nat.shiftLeft (nat_lit 1) (Nat.land y (nat_lit 4095)))))

@[expose] noncomputable def cF (R K LV k : Nat) : Bool := andB (Nat.beq (fxc R) K) (aliveAt LV k (fy R))

@[expose] noncomputable def cB (R K LV k : Nat) : Bool := andB (Nat.beq (fyic R) K) (aliveAt LV k (fx R))

@[expose] noncomputable def wLet (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.mul (nat_lit 8) i)) (nat_lit 255)

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
          (Nat.beq (Nat.land stk (nat_lit 255)) (Nat.succ (wLet inv (wLet w i))))))
      stk (Nat.beq (wLet w i) (nat_lit 255))) n

@[expose] noncomputable def lettersOK (INV w n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (inv16 INV (wLet w i)) (nat_lit 65535))) n

@[expose] noncomputable def sentOK (w n : Nat) : Bool :=
  Nat.beq (Nat.shiftRight w (Nat.mul (nat_lit 8) n)) (nat_lit 1)

@[expose] noncomputable def wRel (INV inv w n r m : Nat) : Bool :=
  andB (lettersOK INV w n) (andB (sentOK w n)
    (orB (Nat.beq (freeRed inv w n) (nat_lit 0)) (isRelRot r m w n)))

@[expose] noncomputable def wSub (INV w n s m : Nat) : Bool :=
  andB (lettersOK INV w n) (andB (sentOK w n)
    (Prod.rec (motive := fun _ => Bool) (fun v k => andB (Nat.beq v s) (Nat.beq k m)) (strip w n)))

@[expose] noncomputable def swarMask (n b : Nat) : Nat :=
  Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 2) b)) (nat_lit 1)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (nat_lit 1))

@[expose] noncomputable def swarStep (n b x : Nat) : Nat :=
  Nat.add (Nat.land x (swarMask n b)) (Nat.land (Nat.shiftRight x b) (swarMask n b))

@[expose] noncomputable def popcount (x n : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul (swarStep n (nat_lit 16) (swarStep n (nat_lit 8)
      (swarStep n (nat_lit 4) (swarStep n (nat_lit 2) (swarStep n (nat_lit 1) x)))))
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) (nat_lit 4294967295)))
    (Nat.sub n (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def pc4096 (x : Nat) : Nat := popcount x (nat_lit 4096)

end CFSG.KC

end
