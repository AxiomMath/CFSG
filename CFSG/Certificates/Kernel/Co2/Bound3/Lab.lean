module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co2.Bound3.F7

public section

namespace CFSG.KC.Co2K

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def lX (L : Nat) : Nat := Nat.land L M1200
@[expose] noncomputable def lXI (L : Nat) : Nat := Nat.land (Nat.shiftRight L (nat_lit 1200)) M1200

@[expose] noncomputable def labOf (X XI : Nat) : Nat := Nat.lor X (Nat.shiftLeft XI (nat_lit 1200))

@[expose] noncomputable def labOne : Nat := labOf ONE7 ONE7

@[expose] noncomputable def pushL (L dir A : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mul7 A (lX L)) (mul7 A (lXI L)) (Nat.beq dir (nat_lit 1))

@[expose] noncomputable def hint (Hs wid : Nat) : Nat :=
  Nat.land (Nat.shiftRight Hs (Nat.mul (nat_lit 16) wid)) (nat_lit 65535)

@[expose] noncomputable def labGo (LB : Nat → Nat) (Li ft n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun k ih R acc => Bool.rec (motive := fun _ => Nat)
      ((fun e => strictN (pushL (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
          (ih (Nat.shiftRight R (nat_lit 32))))
        (Nat.land R (nat_lit 4294967295)))
      (strictN (pushL Li (nat_lit 0) acc) (ih R))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def target (LETs : Nat → Nat) (w h : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) ONE7 (lX (LETs h)) (Nat.beq (wKind w) (nat_lit 3))

@[expose] noncomputable def labWalk (LB LETs : Nat → Nat) (i J w h : Nat) : Bool :=
  letB (LB i) (fun Li =>
    andB (andB (wf7 (lX Li)) (wf7 (lXI Li)))
      (andB (Nat.beq (mul7 (lX Li) (lXI Li)) ONE7)
        (Nat.beq (labGo LB Li (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w) (wLen w)
            (Nat.shiftRight J (nat_lit 53)) ONE7)
          (target LETs w h))))

@[expose] noncomputable def labStep (LB LETs : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (LB (Nat.sub S (nat_lit 1))) labOne))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (labWalk LB LETs (Nat.sub S (nat_lit 1)) J w
          (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunk (WT LB LETs : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStep LB LETs Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStep LB LETs Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLab (WT LB LETs : Nat → Nat) (Hs : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunk WT LB LETs Hs C S) ih) Cs

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
    (fun _ ih R acc => (fun e => strictN (pushL (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
        (ih (Nat.shiftRight R (nat_lit 32))))
      (Nat.land R (nat_lit 4294967295))) k

@[expose] noncomputable def cycOK (blk WT LB : Nat → Nat) (nf c wid R V : Nat) : Bool :=
  letB (WT wid) (fun w => andB (Nat.beq (wKind w) (nat_lit 2))
    (andB (Nat.beq (cycWalk blk nf (wLen w) R (wStart c (wWord w))) (Nat.add c (nat_lit 1048576)))
      (Nat.beq (cycLab LB (wLen w) R ONE7) V)))

end CFSG.KC.Co2K

end
