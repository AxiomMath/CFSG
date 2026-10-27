module

public import CFSG.Certificates.Kernel.Fi22.Fix.Data.Base
public import CFSG.Certificates.Kernel.Common.HOrb

public section

namespace CFSG.KC.Fi22F

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb

@[expose] noncomputable def Lsel (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) CFSG.KD.Fi22F.L3 CFSG.KD.Fi22F.L2 (Nat.beq c (nat_lit 2)))
      CFSG.KD.Fi22F.L1 (Nat.beq c (nat_lit 1)))
    CFSG.KD.Fi22F.L0 (Nat.beq c (nat_lit 0))

@[expose] noncomputable def Esel (g : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) CFSG.KD.Fi22F.E5 CFSG.KD.Fi22F.E4 (Nat.beq g (nat_lit 4)))
          CFSG.KD.Fi22F.E3 (Nat.beq g (nat_lit 3)))
        CFSG.KD.Fi22F.E2 (Nat.beq g (nat_lit 2)))
      CFSG.KD.Fi22F.E1 (Nat.beq g (nat_lit 1)))
    CFSG.KD.Fi22F.E0 (Nat.beq g (nat_lit 0))

@[expose] noncomputable def hBase (S o k : Nat) : Nat := Lsel (wLet (wWord S) (Nat.sub k o))

@[expose] noncomputable def eBase (W n k : Nat) : Nat :=
  Esel (Nat.shiftRight (byte (wWord W) (Nat.sub (Nat.sub n (nat_lit 1)) k)) (nat_lit 1))

end CFSG.KC.Fi22F

end
