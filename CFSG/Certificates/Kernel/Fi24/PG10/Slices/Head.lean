module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P2_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P3_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P4_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P5_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P6_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.KC.LceS

namespace CFSG.KD.PG10P2

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 18) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 9) (nat_lit 32944) (nat_lit 28431) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 32944) = true := by quickRfl

end CFSG.KD.PG10P2

namespace CFSG.KD.PG10P3

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 256) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 16) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 120) (nat_lit 120) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 120) = true := by quickRfl

end CFSG.KD.PG10P3

namespace CFSG.KD.PG10P4

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 14) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 1) (nat_lit 1) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 1) = true := by quickRfl

end CFSG.KD.PG10P4

namespace CFSG.KD.PG10P5

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 12) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 576) (nat_lit 576) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 576) = true := by quickRfl

end CFSG.KD.PG10P5

namespace CFSG.KD.PG10P6

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 64) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 10) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 2520) (nat_lit 2520) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 2520) = true := by quickRfl

end CFSG.KD.PG10P6

end
