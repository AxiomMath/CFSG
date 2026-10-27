module

public import CFSG.Certificates.Kernel.Common.LceS

public section

namespace CFSG.KC.Fi24Act

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def aliveEnum (LVs A : Nat → Nat) (nC N lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) N) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => letB (A i) (fun a => andB (Nat.blt a nC) (andB (alive LVs a)
        (bIf(Nat.blt (Nat.succ i) N, Nat.blt a (A (Nat.succ i)), true)))))
      (Nat.add lo t))) m)

@[expose] noncomputable def slotTo (blk : Nat → Nat) (K r z : Nat) : Bool :=
  letB (fct blk (Nat.shiftRight r (nat_lit 1))) (fun R =>
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq (fxc R) K) (Nat.beq (fy R) z))
      (andB (Nat.beq (fyic R) K) (Nat.beq (fx R) z))
      (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def covTabL (blk A T R : Nat → Nat) (nf c N lo m : Nat) : Bool :=
  andB (Nat.ble (Nat.add lo m) N) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => letB (T i) (fun y => letB (R i) (fun r =>
        andB (Nat.blt y N) (andB (Nat.blt (Nat.shiftRight r (nat_lit 1)) nf)
          (slotTo blk (Nat.lor (A i) (Nat.shiftLeft c (nat_lit 20))) r (A y))))))
      (Nat.add lo t))) m)

end CFSG.KC.Fi24Act

end
