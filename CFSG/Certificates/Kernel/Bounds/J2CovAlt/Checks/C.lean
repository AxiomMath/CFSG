module

public import CFSG.Certificates.Kernel.Bounds.J2CovAlt.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.J2C

open CFSG.KC

theorem sH0 : LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 1024) HS = true := by
  quickRfl

theorem sH1 : LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 222) = true := by
  quickRfl

theorem sH6 : HSK.hintsLt selWT (nat_lit 1024) (nat_lit 1) HS = true := by
  quickRfl

theorem sH7 : LabZ.constsOK (nat_lit 6) BIAS QQ HIGH TOP = true := by
  quickRfl

theorem sH8 : LabZ.tgOK selWT TG INV8 (nat_lit 1024) HS (nat_lit 5) (nat_lit 1) (nat_lit 6) BIAS = true := by
  quickRfl

theorem sW : Nat.beq (LceS.runFacts blk selWT INV nC (nat_lit 4) Cs (LceS.mkS (nat_lit 0) (nat_lit 1)))
    (LceS.mkS (nat_lit 353) (nat_lit 222)) = true := by
  quickRfl

theorem sL : Nat.beq (LabZ.runLabZ selWT LB TG BIAS QQ HIGH TOP Cs (nat_lit 1)) (nat_lit 354) = true := by
  quickRfl

theorem sI : Nat.beq (LceSR.runIds selWT (nat_lit 1024) Cs (nat_lit 1)) (nat_lit 1) = true := by
  quickRfl

theorem cyc_all : ∀ j < 4, cyc j = true := by
  kc_cover 1

end CFSG.KD.J2C

end
