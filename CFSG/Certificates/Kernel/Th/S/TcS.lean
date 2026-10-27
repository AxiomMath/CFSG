module

public import CFSG.Certificates.Kernel.Th.S.Hsw
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.Th.TcS

open CFSG.KC

@[expose] noncomputable def relK (R r : Nat) : Nat := Bool.rec (nat_lit 0) (Hsw.sel r) (Nat.blt r R)

@[expose] noncomputable def subK (K j : Nat) : Nat :=
  Bool.rec (nat_lit 0) (Nat.add (nat_lit 4) (Nat.shiftLeft (Nat.mul (nat_lit 2) j) (nat_lit 12)))
    (Nat.blt j K)

@[expose] noncomputable def litOK (RT : Nat → Nat) (R : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (Nat.beq (RT r) (Hsw.sel r))) R

end CFSG.KC.Th.TcS

end
