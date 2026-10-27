module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X3_Sel
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HSKX3

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 60) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 1) (nat_lit 1) (nat_lit 1) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 1) = true := by
  quickRfl

@[expose] def relMap (_ : Nat) : Nat := CFSG.KC.Bind.ofPairs ((List.range 30).map fun g => (g, g))

@[expose] def sH4r (k : Nat) : Bool := CFSG.KC.Bind.subRel (relMap k) (CFSG.KD.HSKM.XRs k) (litRT k)

#kc_each_unfold CFSG.KD.HSKX3.sH4r 0 87 eval CFSG.KD.HSKX3.relMap

theorem sH5s0 : Nat.beq (litST (nat_lit 0)) (nat_lit 4) = true := by
  quickRfl

theorem sH5s1 : Nat.beq (litST (nat_lit 1)) (nat_lit 8196) = true := by
  quickRfl

theorem sH5s2 : Nat.beq (litST (nat_lit 2)) (nat_lit 16388) = true := by
  quickRfl

end CFSG.KD.HSKX3

end
