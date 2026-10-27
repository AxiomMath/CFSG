module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS

public section

namespace CFSG.KC.Th.OutS

open CFSG.KC.Th CFSG.KC.Loop

@[expose] noncomputable def prodWord (RB : Nat → Nat) (c rm ONE GR IR w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => mulB c rm acc (BigS.letV RB GR IR (BigS.bitsN w (Nat.mul (nat_lit 4) i) (nat_lit 4)))) n

@[expose] noncomputable def sel4 (L0 L1 L2 L3 x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) L3 L2 (Nat.beq x (nat_lit 2)))
    (Bool.rec (motive := fun _ => Nat) L1 L0 (Nat.beq x (nat_lit 0)))
    (Nat.blt x (nat_lit 2))

@[expose] noncomputable def prod4 (c rm L0 L1 L2 L3 S w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun i acc => mulB c rm acc (sel4 L0 L1 L2 L3 (BigS.bitsN w (Nat.mul (nat_lit 2) i) (nat_lit 2)))) n

@[expose] noncomputable def lowBit (x : Nat) : Nat := Nat.sub x (Nat.land x (Nat.sub x (nat_lit 1)))

@[expose] noncomputable def reduce (B k v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v
    (fun i acc => (fun b => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc b)
        (Nat.blt (nat_lit 0) (Nat.land acc (lowBit b))))
      (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 24) i)) rowMask)) k

@[expose] noncomputable def rankStep (M r S : Nat) : Nat :=
  (fun k B => (fun v => Bool.rec (motive := fun _ => Nat) S
      (Nat.lor (Nat.succ k) (Nat.shiftLeft (Nat.lor B (Nat.shiftLeft v (Nat.mul (nat_lit 24) k))) (nat_lit 5)))
      (Nat.blt (nat_lit 0) v))
    (reduce B k (rowOf M r)))
  (Nat.land S (nat_lit 31)) (Nat.shiftRight S (nat_lit 5))

@[expose] noncomputable def rank24 (M : Nat) : Nat :=
  Nat.land (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun r S => rankStep M r S) (nat_lit 24)) (nat_lit 31)

@[expose] noncomputable def invRank (r σ : Nat) : Bool :=
  andB (Nat.beq (mul24 σ σ) ident24) (Nat.beq (rank24 (Nat.xor σ ident24)) r)

@[expose] noncomputable def countA (EB : Nat → Nat) (lo n hi : Nat) : Nat :=
  sumBelow n hi (fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (invRank (nat_lit 6) (DceS.mat EB (Nat.add lo i))))

@[expose] noncomputable def coreOK (EB : Nat → Nat) (LT LI g m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => andB acc ((fun s => orB (Nat.beq s ident24)
        ((fun t => Nat.rec (motive := fun _ => Bool) true
            (fun j acc2 => andB acc2 (Bool.rec (motive := fun _ => Bool) true false
              (Nat.beq t (DceS.mat EB j)))) m)
          (mul24 (mul24 (DceS.let24 LT (DceS.byte LI g)) s) (DceS.let24 LT g))))
      (DceS.mat EB k))) m

@[expose] noncomputable def runClass2 (CB : Nat → Nat) (LT LI TL VL NL : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
        (fun _ ih2 J S => strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
            ((fun k p g => andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt p k) (andB (DceS.isN TL VL NL g)
                (Nat.beq (DceS.mat CB k) (mul24 (mul24 (DceS.let24 LT (DceS.byte LI g)) (DceS.mat CB p)) (DceS.let24 LT g))))))
              (Nat.sub S (nat_lit 1)) (BigS.bitsN J (nat_lit 0) (nat_lit 17)) (BigS.bitsN J (nat_lit 17) (nat_lit 4))))
          (ih2 (Nat.shiftRight J (nat_lit 21))))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

end CFSG.KC.Th.OutS

end
