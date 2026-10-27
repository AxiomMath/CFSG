module

public import CFSG.Certificates.Kernel.He.Bound.Lab

public section

namespace CFSG.KC.HeB

open CFSG.KC CFSG.KC.Loop

@[expose] noncomputable def labWF (K : Nat) : Bool :=
  andB (Nat.blt (kCnt K) (nat_lit 8192))
    (allBelow (kCnt K) (Nat.succ (Nat.shiftRight (kCnt K) (nat_lit 6)))
      (fun k => notB (Nat.beq (kByte K k) (nat_lit 255))))

@[expose] noncomputable def labsWF (LB : Nat → Nat) (nf : Nat) : Bool :=
  allBelow nf (Nat.succ (Nat.shiftRight nf (nat_lit 6))) (fun i => labWF (LB i))

end CFSG.KC.HeB

end
