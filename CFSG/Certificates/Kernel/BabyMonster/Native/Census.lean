module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

public section

namespace CFSG.KC.BM

@[expose] noncomputable def fld32 (T b : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 32) b)) (nat_lit 4294967295)

@[expose] noncomputable def mulT (Ts : List Nat) (k v : Nat) : Nat :=
  (fun base => Nat.xor (fld32 (nthN Ts base) (Nat.land v (nat_lit 255)))
      (Nat.xor (fld32 (nthN Ts (Nat.succ base)) (Nat.land (Nat.shiftRight v (nat_lit 8)) (nat_lit 255)))
        (fld32 (nthN Ts (Nat.succ (Nat.succ base))) (Nat.shiftRight v (nat_lit 16)))))
    (Nat.mul (nat_lit 3) k)

@[expose] noncomputable def lookLB (LB : List (List Nat)) (w : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nthN (nthLL LB (Nat.shiftRight w (nat_lit 20)))
      (Nat.land (Nat.shiftRight w (nat_lit 14)) (nat_lit 63)))
    (Nat.mul (nat_lit 4) (Nat.land w (nat_lit 16383)))) (nat_lit 15)

@[expose] noncomputable def lookDT (DT : List (List Nat)) (w : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nthN (nthLL DT (Nat.shiftRight w (nat_lit 19)))
      (Nat.land (Nat.shiftRight w (nat_lit 13)) (nat_lit 63)))
    (Nat.mul (nat_lit 8) (Nat.land w (nat_lit 8191)))) (nat_lit 255)

@[expose] noncomputable def cnFail : Nat := Nat.shiftLeft (nat_lit 1) (nat_lit 200)

@[expose] noncomputable def censusOne (LB DT : List (List Nat)) (Ts reps : List Nat) (v cnt : Nat) : Nat :=
  (fun a d => Bool.rec (motive := fun _ => Nat) cnFail
      (Nat.add cnt (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 24) (Nat.sub a (nat_lit 1)))))
      (andB (andB (Nat.blt (nat_lit 0) a)
          (andB (Nat.beq (lookLB LB (mulT Ts (nat_lit 0) v)) a) (Nat.beq (lookLB LB (mulT Ts (nat_lit 1) v)) a)))
        (Bool.rec (motive := fun _ => Bool)
          (Nat.beq (Nat.succ (Nat.shiftRight (lookDT DT
              (mulT Ts (Nat.xor (Nat.land d (nat_lit 3)) (nat_lit 2)) v)) (nat_lit 2))) (Nat.shiftRight d (nat_lit 2)))
          (Nat.beq v (nthN reps (Nat.sub a (nat_lit 1))))
          (Nat.beq (Nat.shiftRight d (nat_lit 2)) (nat_lit 0)))))
    (lookLB LB v) (lookDT DT v)

@[expose] noncomputable def censusRange (LB DT : List (List Nat)) (Ts reps : List Nat) (lo len cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih v c => forceB (Bool.rec (motive := fun _ => Nat) (censusOne LB DT Ts reps v c) c (Nat.beq v (nat_lit 0)))
      (fun c' => Bool.rec (motive := fun _ => Nat) (forceB (Nat.succ v) (fun v' => ih v' c')) cnFail (Nat.beq c' cnFail)))
    len lo cnt

@[expose] noncomputable def byteTabOK (M p T : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB ih (Nat.beq (fld32 T b) (vm32 (nat_lit 22) M (Nat.shiftLeft b (Nat.mul (nat_lit 8) p)))))
    (Bool.rec (motive := fun _ => Nat) (nat_lit 256) (nat_lit 64) (Nat.beq p (nat_lit 2)))

end CFSG.KC.BM

end
