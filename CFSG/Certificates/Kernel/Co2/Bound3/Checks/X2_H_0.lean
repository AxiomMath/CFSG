module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X2_Sel
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Co2KX2

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 8) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 6) (nat_lit 22780) (nat_lit 5280) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 22780) = true := by
  quickRfl

@[expose] def relMap (_ : Nat) : Nat := CFSG.KC.Bind.ofPairs ((List.range 4).map fun g => (g, g))

@[expose] def sH4r (k : Nat) : Bool := CFSG.KC.Bind.subRel (relMap k) (CFSG.KD.Co2KM.XRs k) (litRT k)

#kc_each_unfold CFSG.KD.Co2KX2.sH4r 0 13 eval CFSG.KD.Co2KX2.relMap

theorem sH5s0 : Nat.beq (litST (nat_lit 0)) (nat_lit 4) = true := by
  quickRfl

theorem sH5s1 : Nat.beq (litST (nat_lit 1)) (nat_lit 8196) = true := by
  quickRfl

theorem sH5s2 : Nat.beq (litST (nat_lit 2)) (nat_lit 16388) = true := by
  quickRfl

end CFSG.KD.Co2KX2

end
