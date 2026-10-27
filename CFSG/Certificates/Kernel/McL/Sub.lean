module

public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.McL.Perm

public section

namespace CFSG.KC.McL.Sub

open CFSG.KC CFSG.KC.Bind CFSG.KC.McL

@[expose] noncomputable def constF (v : Nat) : Nat → Nat := fun _ => v

@[expose] noncomputable def patch (f : Nat → Nat) (k v : Nat) : Nat → Nat :=
  fun i => Bool.rec (motive := fun _ => Nat) (f i) v (Nat.beq i k)

@[expose] noncomputable def pn (v : Nat) : Nat := Nat.land v (nat_lit 65535)
@[expose] noncomputable def pw (v : Nat) : Nat := Nat.shiftRight v (nat_lit 16)
@[expose] noncomputable def pk (n W : Nat) : Nat := Nat.lor n (Nat.shiftLeft W (nat_lit 16))

@[expose] noncomputable def ofEnt (e : Nat) : Nat := pk (LceS.wLen e) (LceS.wWord e)

@[expose] noncomputable def cat (a b : Nat) : Nat :=
  pk (Nat.add (pn a) (pn b)) (Nat.lor (pw a) (Nat.shiftLeft (pw b) (Nat.mul (nat_lit 8) (pn a))))

@[expose] noncomputable def subst (XT : Nat → Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pk (nat_lit 0) (nat_lit 0))
    (fun q acc => cat acc (XT (wLet (pw v) q))) (pn v)

@[expose] noncomputable def pinvW (v : Nat) : Nat :=
  pk (pn v) (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (Nat.shiftLeft (Nat.xor (wLet (pw v) q) (nat_lit 1))
      (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub (pn v) q) (nat_lit 1))))) (pn v))

@[expose] noncomputable def powW (v k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pk (nat_lit 0) (nat_lit 0)) (fun _ acc => cat acc v) k

@[expose] noncomputable def red (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q P => Bool.rec (motive := fun _ => Nat) (push (nat_lit 1) P (wLet (pw v) q)) P
      (Nat.beq (wLet (pw v) q) (nat_lit 255))) (pn v)

@[expose] noncomputable def stkW (P : Nat) : Nat :=
  pk (kCnt P) (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (kByte P (Nat.sub (kCnt P) (Nat.succ q))) (nat_lit 1))
      (Nat.mul (nat_lit 8) q))) (kCnt P))

@[expose] noncomputable def redEq (u v : Nat) : Bool := Nat.beq (red u) (red v)

@[expose] noncomputable def xtOK (XT : Nat → Nat) : Bool :=
  andB (Nat.beq (XT (nat_lit 0)) (pk (nat_lit 1) (nat_lit 0)))
    (andB (Nat.beq (XT (nat_lit 2)) (pk (nat_lit 3) (nat_lit 131075)))
      (andB (Nat.beq (XT (nat_lit 4)) (pk (nat_lit 5) (nat_lit 12935234050)))
        (andB (Nat.beq (XT (nat_lit 6)) (pk (nat_lit 3) (nat_lit 196610)))
          (Nat.rec (motive := fun _ => Bool) true
            (fun g acc => andB acc (Nat.beq (XT (Nat.add (Nat.mul (nat_lit 2) g) (nat_lit 1)))
              (pinvW (XT (Nat.mul (nat_lit 2) g))))) (nat_lit 4)))))

@[expose] noncomputable def pl (v q : Nat) : Nat := wLet (pw v) q

@[expose] noncomputable def isConjRot (e ul v : Nat) : Bool :=
  andB (Nat.beq (pn v) (Nat.add (Nat.mul (nat_lit 2) ul) (LceS.wLen e)))
    (andB (Nat.rec (motive := fun _ => Bool) true
        (fun q acc => andB acc (Nat.beq (Nat.xor (pl v q) (nat_lit 1)) (pl v (Nat.sub (pn v) (Nat.succ q))))) ul)
      (andB (Nat.blt (nat_lit 0) (LceS.wLen e))
        (isRot (LceS.wWord e) (LceS.wLen e)
          (Nat.land (Nat.shiftRight (pw v) (Nat.mul (nat_lit 8) ul))
            (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (LceS.wLen e))) (nat_lit 1))))))

@[expose] noncomputable def conjRelOK (RT : Nat → Nat) (R r ul v : Nat) : Bool :=
  andB (Nat.blt r R) (isConjRot (RT r) ul (stkW (red v)))

@[expose] noncomputable def bindRun (XT REL TW TL : Nat → Nat) (NR nT L1 L2 m J S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => (fun r k => ih (Nat.shiftRight J (nat_lit 24))
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.lor S (Nat.shiftLeft (nat_lit 2) r))
          (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt r NR) (andB (Nat.blt k nT)
            (andB (orB (Nat.beq (TL k) L1) (Nat.beq (TL k) L2))
              (redEq (subst XT (ofEnt (REL r))) (ofEnt (TW k)))))))))
      (Nat.land J (nat_lit 255)) (Nat.land (Nat.shiftRight J (nat_lit 8)) (nat_lit 65535))) m J S

@[expose] noncomputable def pinv (d p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul (nat_lit 6) (pget p i)))) d

@[expose] noncomputable def gensOK (G : Nat → Nat) (d g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (pairOK d (G (Nat.mul (nat_lit 2) i)) (G (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1))))) g

@[expose] noncomputable def relsHold (G REL : Nat → Nat) (d NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r acc => andB acc (Nat.beq (evalW G d (LceS.wWord (REL r)) (LceS.wLen (REL r))) (pid d))) NR

@[expose] noncomputable def evenLens (REL : Nat → Nat) (NR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r acc => andB acc (Nat.beq (Nat.land (LceS.wLen (REL r)) (nat_lit 1)) (nat_lit 0))) NR

@[expose] noncomputable def subOK (XT G ST SL SN SH TWm TLm : Nat → Nat) (d nTm Lm j : Nat) : Bool :=
  andB (Nat.beq (SL j) (evalW G d (LceS.wWord (SN j)) (LceS.wLen (SN j))))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        ((fun k => andB (Nat.blt k nTm) (andB (Nat.beq (TLm k) Lm)
            (redEq (cat (ofEnt (ST j)) (pinvW (subst XT (ofEnt (SN j))))) (ofEnt (TWm k)))))
          (Nat.shiftRight (SH j) (nat_lit 1)))
        (Nat.beq (Nat.land (SH j) (nat_lit 1)) (nat_lit 1)))
      (redEq (ofEnt (ST j)) (subst XT (ofEnt (SN j))))
      (Nat.beq (SH j) (nat_lit 0)))

@[expose] noncomputable def subsOK (XT G ST SL SN SH TWm TLm : Nat → Nat) (d nTm Lm K : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j acc => andB acc (subOK XT G ST SL SN SH TWm TLm d nTm Lm j)) K

@[expose] noncomputable def anchorOK (RT ST SL : Nat → Nat) (R n r ul : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) n) (andB (Nat.beq (SL (nat_lit 0)) (pcyc n))
    (conjRelOK RT R r ul (powW (ofEnt (ST (nat_lit 0))) n)))

@[expose] noncomputable def k1Run (XT G TW TL S Q H : Nat → Nat) (d nT m K : Nat) : Bool :=
  (fun res => andB (Nat.beq (Nat.land res (nat_lit 1)) (nat_lit 1))
      (andB (Nat.beq (Nat.land (Nat.shiftRight res (nat_lit 1)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 6) d)) (nat_lit 1))) (pid d))
        (Nat.beq (Nat.shiftRight res (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d))) K)))
    (Nat.rec (motive := fun _ => Nat)
      (Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (pid d) (nat_lit 1)) (Nat.shiftLeft (pid d) (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))))
      (fun i acc => (fun k sg => (fun X Y s q =>
          (fun ms mq => Nat.lor
              (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
                (andB (Nat.beq (Nat.land acc (nat_lit 1)) (nat_lit 1)) (andB (Nat.blt k nT)
                  (redEq (cat (cat (cat (XT (nat_lit 6)) (subst XT s)) (XT (nat_lit 6))) (subst XT (pinvW q)))
                    (ofEnt (TW k))))))
              (Nat.lor (Nat.shiftLeft (pmul d X (Bool.rec (motive := fun _ => Nat) ms (pinv d ms) sg)) (nat_lit 1))
                (Nat.shiftLeft (pmul d Y (Bool.rec (motive := fun _ => Nat) (pmul d (TL k) mq) (pinv d (pmul d (TL k) mq)) sg))
                  (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))))
            (evalW G d (pw s) (pn s)) (evalW G d (pw q) (pn q)))
          (Nat.land (Nat.shiftRight acc (nat_lit 1)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 6) d)) (nat_lit 1)))
          (Nat.shiftRight acc (Nat.add (nat_lit 1) (Nat.mul (nat_lit 6) d)))
          (ofEnt (S i)) (ofEnt (Q i)))
        (Nat.shiftRight (H i) (nat_lit 1)) (Nat.beq (Nat.land (H i) (nat_lit 1)) (nat_lit 1))) m)

end CFSG.KC.McL.Sub

end
