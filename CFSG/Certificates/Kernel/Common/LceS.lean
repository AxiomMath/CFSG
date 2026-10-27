module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.LceS

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def fct (blk : Nat → Nat) (h : Nat) : Nat :=
  strictN (Nat.shiftRight h (nat_lit 8)) (fun k =>
    rget (blk k) (Nat.mul (Nat.land h (nat_lit 255)) (nat_lit 56)))

@[expose] noncomputable def sI (S : Nat) : Nat := Nat.land S (nat_lit 4294967295)
@[expose] noncomputable def sN (S : Nat) : Nat := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkS (i nx : Nat) : Nat := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def wKind (w : Nat) : Nat := Nat.land w (nat_lit 3)
@[expose] noncomputable def wLen (w : Nat) : Nat := Nat.land (Nat.shiftRight w (nat_lit 2)) (nat_lit 1023)
@[expose] noncomputable def wWord (w : Nat) : Nat := Nat.shiftRight w (nat_lit 12)

@[expose] noncomputable def refStep (blk : Nat → Nat) (i e st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (strictN (fct blk (Nat.shiftRight e (nat_lit 1))) (fun R =>
      Bool.rec (motive := fun _ => Nat) (sF R st) (sB R st)
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))
    (Nat.blt (Nat.shiftRight e (nat_lit 1)) i)

@[expose] noncomputable def walkGo (blk : Nat → Nat) (i Ri ft n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun k ih J st => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 32)) (refStep blk i (Nat.land J (nat_lit 4294967295)) st))
      (ih J (sF Ri st))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def jLen (J w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 1)
    (Nat.add (nat_lit 53) (Nat.mul (nat_lit 32) (Nat.sub (wLen w) (nat_lit 1))))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def walkOK (blk : Nat → Nat) (INV nC i R w fs ft J : Nat) : Bool :=
  andB (recOK INV nC R) (andB (Nat.blt ft (wLen w))
    (andB (orB (Nat.beq (wKind w) (nat_lit 2)) (andB (Nat.beq (wKind w) (nat_lit 3)) (Nat.beq fs (nat_lit 0))))
      (Nat.beq (walkGo blk i R ft (wLen w) (wLen w) (Nat.shiftRight J (nat_lit 53)) (wStart fs (wWord w)))
        (Nat.add fs (nat_lit 1048576)))))

@[expose] noncomputable def factStep (blk : Nat → Nat) (INV nC L J S R w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (Nat.succ (sN S)))
        (fTree INV nC L R (sN S)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkS (Nat.succ (sI S)) (sN S))
        (walkOK blk INV nC (sI S) R w
          (Nat.land (Nat.shiftRight J (nat_lit 17)) (nat_lit 1048575))
          (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) J))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def runChunk (blk WT : Nat → Nat) (INV nC L C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) (factStep blk INV nC L J S (fct blk (sI S)) (nat_lit 0)))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        ih (Nat.shiftRight J (jLen J w)) (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runFacts (blk WT : Nat → Nat) (INV nC L : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (runChunk blk WT INV nC L C S) ih) Cs

@[expose] noncomputable def alive (LVs : Nat → Nat) (y : Nat) : Bool :=
  letB (Nat.shiftRight y (nat_lit 12)) (fun k =>
    Nat.blt (nat_lit 0) (Nat.land (LVs k) (Nat.shiftLeft (nat_lit 1) (Nat.land y (nat_lit 4095)))))

@[expose] noncomputable def slotOK (blk LVs : Nat → Nat) (nf K e : Nat) : Bool :=
  andB (Nat.blt (Nat.shiftRight e (nat_lit 1)) nf)
    (letB (fct blk (Nat.shiftRight e (nat_lit 1))) (fun R =>
      Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (fxc R) K) (alive LVs (fy R)))
        (andB (Nat.beq (fyic R) K) (alive LVs (fx R)))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def slotsOK (blk LVs : Nat → Nat) (nf L x J : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih J => andB
      (slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft (Nat.sub L (Nat.succ k)) (nat_lit 20)))
        (Nat.land J (nat_lit 4294967295)))
      (letB (Nat.shiftRight J (nat_lit 32)) ih)) L J

@[expose] noncomputable def covStep (blk LVs : Nat → Nat) (nf L J X : Nat) (a : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat) (Nat.succ X)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ X)
        (slotsOK blk LVs nf L (Nat.sub X (nat_lit 1)) J))
      a)
    (Nat.blt (nat_lit 0) X)

@[expose] noncomputable def covChunk (blk LVs : Nat → Nat) (nf L C X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ X => X)
    (fun _ ih J X =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (covStep blk LVs nf L J X false) (ih J))
        (strictN (covStep blk LVs nf L J X true) (fun X' =>
          strictN (Nat.shiftRight J (Nat.mul (nat_lit 32) L)) (fun J' => ih J' X')))
        (alive LVs (Nat.sub X (nat_lit 1))))
    (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) X

@[expose] noncomputable def runCover (blk LVs : Nat → Nat) (nf L : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun C _ ih X => strictN (covChunk blk LVs nf L C X) ih) Cs

@[expose] noncomputable def wordsOK (WT RT ST : Nat → Nat) (INV INV8 m Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k ih H => andB
      ((fun w r => Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true
            (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r)))
            (Nat.beq (wKind w) (nat_lit 3)))
          (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
          (Nat.beq (wKind w) (nat_lit 2)))
        (WT (Nat.sub m (Nat.succ k))) (Nat.land H (nat_lit 65535)))
      (ih (Nat.shiftRight H (nat_lit 16)))) m Hs

@[expose] noncomputable def invOK (INV INV8 L : Nat) : Bool :=
  andB (Nat.blt L (nat_lit 255)) (andB (Nat.beq (Nat.land L (nat_lit 1)) (nat_lit 0))
    (andB (Nat.blt INV (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)))
      (andB (Nat.blt INV8 (Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))
        (Nat.rec (motive := fun _ => Bool) true (fun c ih => andB
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (andB (Nat.beq (inv16 INV c) (nat_lit 65535)) (Nat.beq (wLet INV8 c) (nat_lit 254)))
              (andB (Nat.beq (inv16 INV c) (nat_lit 255)) (Nat.beq (wLet INV8 c) (nat_lit 255)))
              (Nat.beq c (nat_lit 255)))
            (andB (Nat.beq (inv16 INV c) (Nat.xor c (nat_lit 1))) (Nat.beq (wLet INV8 c) (Nat.xor c (nat_lit 1))))
            (Nat.blt c L)) ih) (nat_lit 256)))))

@[expose] noncomputable def aliveOK (LVs : Nat → Nat) (m nC a : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight (Nat.add nC (nat_lit 4095)) (nat_lit 12)) m)
    (andB (Nat.beq (Nat.shiftRight (LVs (Nat.sub m (nat_lit 1)))
        (Nat.sub nC (Nat.mul (nat_lit 4096) (Nat.sub m (nat_lit 1))))) (nat_lit 0))
      (andB (alive LVs (nat_lit 0))
        (Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun k ih => Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1048576) ih)
            (Nat.add (pc4096 (LVs k)) ih)
            (Nat.blt (LVs k) (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)))) m) a)))

end CFSG.KC.LceS

end
