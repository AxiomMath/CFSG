module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X3_Sel
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Fi22KX3

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 256) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 12) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 3) (nat_lit 9794) (nat_lit 8064) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 9794) = true := by
  quickRfl

@[expose] def relMap (_ : Nat) : Nat := CFSG.KC.Bind.ofPairs ((List.range 6).map fun g => (g, g))

@[expose] def relIx (k : Nat) : Nat :=
  [0, 1, 2, 3, 20, 13, 4, 5, 6, 21, 14, 7, 22, 15, 8, 17, 10, 23, 24, 25, 26, 18, 19].getD k 0

@[expose] def sH4r (k : Nat) : Bool :=
  CFSG.KC.Bind.subRel (relMap k) (CFSG.KD.Fi22KM.XRs (relIx k)) (litRT k)

#kc_each_unfold CFSG.KD.Fi22KX3.sH4r 0 23 eval CFSG.KD.Fi22KX3.relMap CFSG.KD.Fi22KX3.relIx

theorem sH5s0 : Nat.beq (litST (nat_lit 0)) (nat_lit 4) = true := by
  quickRfl

theorem sH5s1 : Nat.beq (litST (nat_lit 1)) (nat_lit 8196) = true := by
  quickRfl

theorem sH5s2 : Nat.beq (litST (nat_lit 2)) (nat_lit 16388) = true := by
  quickRfl

theorem sH5s3 : Nat.beq (litST (nat_lit 3)) (nat_lit 24580) = true := by
  quickRfl

theorem sH5s4 : Nat.beq (litST (nat_lit 4)) (nat_lit 40964) = true := by
  quickRfl

end CFSG.KD.Fi22KX3

end
