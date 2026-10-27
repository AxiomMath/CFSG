module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Rels

public section

namespace CFSG.KC.RuB

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

@[expose] noncomputable def kCnt (K : Nat) : Nat := Nat.land K (nat_lit 16777215)
@[expose] noncomputable def kStk (K : Nat) : Nat := Nat.shiftRight K (nat_lit 24)
@[expose] noncomputable def mkK (c s : Nat) : Nat := Nat.lor c (Nat.shiftLeft s (nat_lit 24))

@[expose] noncomputable def kByte (K i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (kStk K) (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def labInv (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.xor x (nat_lit 1)) (nat_lit 2) (Nat.beq x (nat_lit 2))

@[expose] noncomputable def lpush (K x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mkK (Nat.succ (kCnt K)) (Nat.add (Nat.mul (kStk K) (nat_lit 256)) (Nat.succ x)))
    (mkK (Nat.sub (kCnt K) (nat_lit 1)) (Nat.shiftRight (kStk K) (nat_lit 8)))
    (andB (Nat.blt (nat_lit 0) (kCnt K))
      (Nat.beq (Nat.land (kStk K) (nat_lit 255)) (Nat.succ (labInv x))))

@[expose] noncomputable def pushFwd (L acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush a (Nat.sub (kByte L k) (nat_lit 1))) ih) (kCnt L) acc

@[expose] noncomputable def pushInv (L acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush a (labInv (Nat.sub (kByte L (Nat.sub (Nat.sub (kCnt L) (nat_lit 1)) k))
      (nat_lit 1)))) ih) (kCnt L) acc

@[expose] noncomputable def pushLab (L dir acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pushFwd L acc) (pushInv L acc) (Nat.beq dir (nat_lit 1))

@[expose] noncomputable def hint (Hs wid : Nat) : Nat :=
  Nat.land (Nat.shiftRight Hs (Nat.mul (nat_lit 16) wid)) (nat_lit 65535)

@[expose] noncomputable def labGo (LB : Nat → Nat) (Li ft n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun k ih R acc => Bool.rec (motive := fun _ => Nat)
      ((fun e => strictN (pushLab (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
          (ih (Nat.shiftRight R (nat_lit 32))))
        (Nat.land R (nat_lit 4294967295)))
      (strictN (pushFwd Li acc) (ih R))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def target (w h : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (mkK (nat_lit 1) (Nat.succ (subLet h)))
    (Nat.beq (wKind w) (nat_lit 3))

@[expose] noncomputable def labWalk (LB : Nat → Nat) (i J w h : Nat) : Bool :=
  Nat.beq (labGo LB (LB i) (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w) (wLen w)
      (Nat.shiftRight J (nat_lit 53)) (nat_lit 0))
    (target w h)

@[expose] noncomputable def labStep (LB : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (LB (Nat.sub S (nat_lit 1))) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (labWalk LB (Nat.sub S (nat_lit 1)) J w
          (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunk (WT LB : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStep LB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStep LB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLab (WT LB : Nat → Nat) (Hs : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunk WT LB Hs C S) ih) Cs

@[expose] noncomputable def hintsLt (WT : Nat → Nat) (m K Hs : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (Bool.rec (motive := fun _ => Bool) true (Nat.blt (hint Hs k) K) (Nat.beq (wKind (WT k)) (nat_lit 3)))) m

@[expose] noncomputable def litOK (RT ref : Nat → Nat) (R : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (Nat.beq (RT r) (ref r))) R

@[expose] noncomputable def cycWalk (blk : Nat → Nat) (nf : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun _ ih R st => strictN (refStep blk nf (Nat.land R (nat_lit 4294967295)) st)
      (ih (Nat.shiftRight R (nat_lit 32)))) k

@[expose] noncomputable def cycLab (LB : Nat → Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih R acc => (fun e => strictN (pushLab (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
        (ih (Nat.shiftRight R (nat_lit 32))))
      (Nat.land R (nat_lit 4294967295))) k

@[expose] noncomputable def cycRed (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun P => P) (fun _ ih P =>
    Bool.rec (motive := fun _ => Nat) P
      (strictN (mkK (Nat.sub (kCnt P) (nat_lit 2))
        (Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft (nat_lit 1)
          (Nat.mul (nat_lit 8) (Nat.sub (kCnt P) (nat_lit 1)))) (nat_lit 1))) (nat_lit 8))) ih)
      (andB (Nat.ble (nat_lit 2) (kCnt P))
        (Nat.beq (kByte P (Nat.sub (kCnt P) (nat_lit 1)))
          (Nat.succ (labInv (Nat.sub (kByte P (nat_lit 0)) (nat_lit 1)))))))
    (Nat.shiftRight (kCnt K) (nat_lit 1)) K

@[expose] noncomputable def cycOK (blk WT LB : Nat → Nat) (nf c wid R rho : Nat) : Bool :=
  letB (WT wid) (fun w => andB (Nat.beq (wKind w) (nat_lit 2))
    (andB (Nat.beq (cycWalk blk nf (wLen w) R (wStart c (wWord w))) (Nat.add c (nat_lit 1048576)))
      (Nat.beq (cycRed (cycLab LB (wLen w) R (nat_lit 0))) rho)))

@[expose] noncomputable def entStk (E : Nat) : Nat :=
  mkK (wLen E) (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun k ih s => strictN (Nat.add (Nat.mul s (nat_lit 256))
      (Nat.succ (wLet (wWord E) (Nat.sub (Nat.sub (wLen E) (nat_lit 1)) k)))) ih) (wLen E) (nat_lit 0))

end CFSG.KC.RuB

end
