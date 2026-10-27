module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.McL.Perm

public section

namespace CFSG.KC.McL.Lab

open CFSG.KC CFSG.KC.Loop CFSG.KC.McL

@[expose] noncomputable def m20 : Nat := nat_lit 1048575
@[expose] noncomputable def m28 : Nat := nat_lit 268435455
@[expose] noncomputable def m32 : Nat := nat_lit 4294967295

@[expose] noncomputable def rx (R : Nat) : Nat := Nat.land R m20
@[expose] noncomputable def rc (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 20)) (nat_lit 255)
@[expose] noncomputable def ry (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 28)) m20
@[expose] noncomputable def ric (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 48)) (nat_lit 255)
@[expose] noncomputable def rxc (R : Nat) : Nat := Nat.land R m28
@[expose] noncomputable def ryic (R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 28)) m28
@[expose] noncomputable def rlab (lm R : Nat) : Nat := Nat.land (Nat.shiftRight R (nat_lit 56)) lm
@[expose] noncomputable def rlabI (lw lm R : Nat) : Nat := Nat.land (Nat.shiftRight R (Nat.add (nat_lit 56) lw)) lm

@[expose] noncomputable def fct (FB : Nat → Nat) (rw h : Nat) : Nat :=
  strictN (Nat.shiftRight h (nat_lit 6)) (fun k =>
    Nat.shiftRight (FB k) (Nat.mul (Nat.sub h (Nat.shiftLeft k (nat_lit 6))) rw))

@[expose] noncomputable def sF (R st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Nat.lor (ry R) (Nat.shiftLeft (Nat.shiftRight st (nat_lit 28)) (nat_lit 20)))
    (Nat.beq (Nat.land st m28) (rxc R))

@[expose] noncomputable def sB (R st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Nat.lor (rx R) (Nat.shiftLeft (Nat.shiftRight st (nat_lit 28)) (nat_lit 20)))
    (Nat.beq (Nat.land st m28) (ryic R))

@[expose] noncomputable def recOK (INV d lw lm nC R : Nat) : Bool :=
  andB (Nat.blt (rx R) nC) (andB (Nat.blt (ry R) nC)
    (andB (Nat.beq (ric R) (inv16 INV (rc R))) (pairOK d (rlab lm R) (rlabI lw lm R))))

@[expose] noncomputable def refStep (FB : Nat → Nat) (rw d lw lm hi e st A : Nat) (k : Nat → Nat → Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (k (nat_lit 0) A)
    (strictN (fct FB rw (Nat.shiftRight e (nat_lit 1))) (fun R =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (sF R st) (fun st' => strictN (pmul d A (rlab lm R)) (k st')))
        (strictN (sB R st) (fun st' => strictN (pmul d A (rlabI lw lm R)) (k st')))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))
    (Nat.blt (Nat.shiftRight e (nat_lit 1)) hi)

@[expose] noncomputable def walkGo (FB : Nat → Nat) (rw d lw lm i Ri ft n : Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ st A => Nat.lor A (Nat.shiftLeft st lw))
    (fun k ih J st A => Bool.rec (motive := fun _ => Nat)
      (refStep FB rw d lw lm i (Nat.land J m32) st A (ih (Nat.shiftRight J (nat_lit 32))))
      (strictN (sF Ri st) (fun st' => strictN (pmul d A (rlab lm Ri)) (ih J st')))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def wKind (w : Nat) : Nat := Nat.land w (nat_lit 3)
@[expose] noncomputable def wLen (w : Nat) : Nat := Nat.land (Nat.shiftRight w (nat_lit 2)) (nat_lit 1023)
@[expose] noncomputable def wHint (w : Nat) : Nat := Nat.land (Nat.shiftRight w (nat_lit 12)) (nat_lit 65535)
@[expose] noncomputable def wWord (w : Nat) : Nat := Nat.shiftRight w (nat_lit 28)

@[expose] noncomputable def wTarget (SL : Nat → Nat) (d w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pid d) (SL (wHint w)) (Nat.beq (wKind w) (nat_lit 3))

@[expose] noncomputable def walkOK (FB SL : Nat → Nat) (INV rw d lw lm nC i R w fs ft J : Nat) : Bool :=
  andB (recOK INV d lw lm nC R) (andB (Nat.blt ft (wLen w))
    (andB (orB (Nat.beq (wKind w) (nat_lit 2)) (andB (Nat.beq (wKind w) (nat_lit 3)) (Nat.beq fs (nat_lit 0))))
      ((fun res => andB (Nat.beq (Nat.shiftRight res lw) (Nat.add fs (nat_lit 1048576)))
          (Nat.beq (Nat.land res lm) (wTarget SL d w)))
        (walkGo FB rw d lw lm i R ft (wLen w) (wLen w) (Nat.shiftRight J (nat_lit 53))
          (wStart fs (wWord w)) (pid d)))))

@[expose] noncomputable def treeOK (INV d lw lm nC L nx R : Nat) : Bool :=
  andB (recOK INV d lw lm nC R) (andB (Nat.beq (ry R) nx) (andB (Nat.blt (rx R) nx)
    (andB (Nat.blt (rc R) L) (andB (Nat.beq (rlab lm R) (pid d)) (Nat.beq (rlabI lw lm R) (pid d))))))

@[expose] noncomputable def sI (S : Nat) : Nat := Nat.land S m32
@[expose] noncomputable def sN (S : Nat) : Nat := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkS (i nx : Nat) : Nat := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def factStep (FB SL : Nat → Nat) (INV rw d lw lm nC L J S w : Nat) : Nat :=
  (fun R => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (Nat.succ (sN S)))
        (treeOK INV d lw lm nC L (sN S) R))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (sN S))
        (walkOK FB SL INV rw d lw lm nC (sI S) R w
          (Nat.land (Nat.shiftRight J (nat_lit 17)) m20)
          (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) J))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S))
  (fct FB rw (sI S))

@[expose] noncomputable def jLen (J w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 1)
    (Nat.add (nat_lit 53) (Nat.mul (nat_lit 32) (Nat.sub (wLen w) (nat_lit 1))))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def runChunk (FB WT SL : Nat → Nat) (INV rw d lw lm nC L C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) (factStep FB SL INV rw d lw lm nC L J S (nat_lit 0)))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (factStep FB SL INV rw d lw lm nC L J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (FB WT SL : Nat → Nat) (INV rw d lw lm nC L : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk FB WT SL INV rw d lw lm nC L C S) ih) Cs

@[expose] noncomputable def wordOK (RT ST : Nat → Nat) (INV INV8 R K w : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false
      (andB (Nat.blt (wHint w) K)
        (wSub INV (wWord w) (wLen w) (LceS.wWord (ST (wHint w))) (LceS.wLen (ST (wHint w)))))
      (Nat.beq (wKind w) (nat_lit 3)))
    (andB (Nat.blt (wHint w) R)
      (wRel INV INV8 (wWord w) (wLen w) (LceS.wWord (RT (wHint w))) (LceS.wLen (RT (wHint w)))))
    (Nat.beq (wKind w) (nat_lit 2))

@[expose] noncomputable def wordsOK (WT RT ST : Nat → Nat) (INV INV8 R K m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun w ih => andB ih (wordOK RT ST INV INV8 R K (WT w))) m

@[expose] noncomputable def traceGo (FB : Nat → Nat) (rw d lw lm nF : Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ st A => Nat.lor A (Nat.shiftLeft st lw))
    (fun _ ih J st A => refStep FB rw d lw lm nF (Nat.land J m32) st A (ih (Nat.shiftRight J (nat_lit 32)))) k

@[expose] noncomputable def targetOK (FB TW TL : Nat → Nat) (rw d lw lm nF k J : Nat) : Bool :=
  (fun e => (fun n => andB (Nat.blt (nat_lit 0) n)
      ((fun res => andB (Nat.beq (Nat.shiftRight res lw) (nat_lit 1048576)) (Nat.beq (Nat.land res lm) (TL k)))
        (traceGo FB rw d lw lm nF n J
          (wStart (nat_lit 0) (Nat.lor (LceS.wWord e) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) n))))
          (pid d))))
    (LceS.wLen e)) (TW k)

@[expose] noncomputable def runTargets (FB TW TL : Nat → Nat) (rw d lw lm nF : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            (andB (Nat.blt (nat_lit 0) S) (targetOK FB TW TL rw d lw lm nF (Nat.sub S (nat_lit 1)) J)))
          (ih2 (Nat.shiftRight J (Nat.mul (nat_lit 32) (LceS.wLen (TW (Nat.sub S (nat_lit 1))))))))
        (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S) ih) Cs

end CFSG.KC.McL.Lab

end
