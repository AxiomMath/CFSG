module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.HNAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNAlg

theorem comb : Nat.beq (CFSG.KC.Fam.lincomb RW 5 13 9 L H RWn [1793, 2051, 514, 2820, 3073]) Cm =
    true := by
  quickRfl

theorem rnull : Nat.beq (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM Cm C0v) 0 = true := by
  quickRfl

theorem lnull : Nat.beq (CFSG.KC.Ord.vecR 5 13 1729 133 9 LV HV RM urow Cm) 0 = true := by
  quickRfl

theorem nz : CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq vrow 0))
    (CFSG.KC.Ord.notB (Nat.beq urow 0)) = true := by
  quickRfl

theorem vcol : Nat.beq (Nat.land C0v CM) C0v = true := by
  quickRfl

theorem vrowcol : Nat.beq C0v (CFSG.KC.Fam.colOf 13 1729 133 vrow) = true := by
  quickRfl

theorem rker : CFSG.KC.Fam.rkerOK 5 13 9 L H CM ONE (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) (CFSG.KC.Ord.validM 5 1729 LV HV) Cm Ym C0v uprow = true := by
  quickRfl

end CFSG.KD.FamHNAlg

end
