module

public import CFSG.Certificates.Kernel.Bounds.M22CovAlt.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.M22C

open CFSG.KC

theorem sH0 : LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 1429) = true := by
  quickRfl

theorem sH6 : HSK.hintsLt selWT (nat_lit 512) (nat_lit 1) HS = true := by
  quickRfl

theorem sH7 : LabZ.constsOK (nat_lit 9) BIAS QQ HIGH TOP = true := by
  quickRfl

theorem sH8 : LabZ.tgOK selWT TG INV8 (nat_lit 512) HS (nat_lit 8) (nat_lit 1) (nat_lit 9) BIAS = true := by
  quickRfl

theorem sW : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 4) Cs (LceS.mkS (nat_lit 0) (nat_lit 1)))
    (LceS.mkS (nat_lit 2129) (nat_lit 1429)) = true := by
  quickRfl

theorem sL : Nat.beq (LabZ.runLabZ selWT LB TG BIAS QQ HIGH TOP Cs (nat_lit 1)) (nat_lit 2130) = true := by
  quickRfl

theorem sI : Nat.beq (LceSR.runIds selWT (nat_lit 512) Cs (nat_lit 1)) (nat_lit 1) = true := by
  quickRfl

theorem cyc_all : ∀ j < 7, cyc j = true := by
  kc_cover 1

end CFSG.KD.M22C

end
