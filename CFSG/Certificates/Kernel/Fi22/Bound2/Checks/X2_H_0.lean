module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X2_Sel
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi22KX2

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 10) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 1) (nat_lit 4008) (nat_lit 3960) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 4008) = true := by
  quickRfl

@[expose] def relMap (_ : Nat) : Nat :=
  CFSG.KC.Bind.ofPairs [(0, 0), (1, 1), (2, 2), (3, 3), (5, 4)]

@[expose] def relIx (k : Nat) : Nat :=
  [0, 1, 2, 3, 13, 4, 5, 6, 14, 7, 15, 8, 16, 17, 9, 10, 18, 19].getD k 0

@[expose] def sH4r (k : Nat) : Bool :=
  CFSG.KC.Bind.subRel (relMap k) (CFSG.KD.Fi22KM.XRs (relIx k)) (litRT k)

#kc_each_unfold CFSG.KD.Fi22KX2.sH4r 0 18 eval CFSG.KD.Fi22KX2.relMap CFSG.KD.Fi22KX2.relIx

theorem sH5s0 : Nat.beq (litST (nat_lit 0)) (nat_lit 4) = true := by
  quickRfl

theorem sH5s1 : Nat.beq (litST (nat_lit 1)) (nat_lit 8196) = true := by
  quickRfl

theorem sH5s2 : Nat.beq (litST (nat_lit 2)) (nat_lit 16388) = true := by
  quickRfl

theorem sH5s3 : Nat.beq (litST (nat_lit 3)) (nat_lit 24580) = true := by
  quickRfl

end CFSG.KD.Fi22KX2

end
