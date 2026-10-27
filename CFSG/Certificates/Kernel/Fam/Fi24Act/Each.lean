module

public import CFSG.Certificates.Kernel.Fam.Fi24Act.Lib
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.Sel
public import CFSG.Certificates.Kernel.Fam.Fi24Act.Data.SelJL
public import CFSG.Certificates.Kernel.Fi24.Data.F1_Sel

public noncomputable section

namespace CFSG.KD.FamFi24Act

@[expose] def chunkLen (k : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 248 512 (Nat.blt k 599)

@[expose] def alC (k : Nat) : Bool :=
  CFSG.KC.Fi24Act.aliveEnum CFSG.KD.F1.LVs TA CFSG.KD.F1.nC 306936 (Nat.mul 512 k) (chunkLen k)

@[expose] def covG (T R : Nat → Nat) (c k : Nat) : Bool :=
  CFSG.KC.Fi24Act.covTabL CFSG.KD.F1.blk TA T R 6653548 c 306936 (Nat.mul 512 k) (chunkLen k)

@[expose] def cov0C (k : Nat) : Bool := covG T0 R0 0 k
@[expose] def cov1C (k : Nat) : Bool := covG T1 R1 2 k
@[expose] def cov2C (k : Nat) : Bool := covG T2 R2 4 k
@[expose] def cov3C (k : Nat) : Bool := covG T3 R3 6 k
@[expose] def cov4C (k : Nat) : Bool := covG T4 R4 8 k
@[expose] def cov5C (k : Nat) : Bool := covG T5 R5 10 k
@[expose] def cov6C (k : Nat) : Bool := covG T6 R6 12 k
@[expose] def cov7C (k : Nat) : Bool := covG T7 R7 14 k
@[expose] def cov8C (k : Nat) : Bool := covG T8 R8 16 k
@[expose] def cov9C (k : Nat) : Bool := covG T9 R9 20 k
@[expose] def covJC (k : Nat) : Bool := covG TJ RJ 18 k
@[expose] def covLC (k : Nat) : Bool := covG TL RL 22 k

end CFSG.KD.FamFi24Act

end
