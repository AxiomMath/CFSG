module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.F3_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F4_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F5_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F6_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F7_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F8_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F9_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F10_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F11_Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.KC.LceS

namespace CFSG.KD.F3

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 18) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 12) (nat_lit 46382) (nat_lit 28431) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 46382) = true := by quickRfl

end CFSG.KD.F3

namespace CFSG.KD.F4

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 16) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 120) (nat_lit 120) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 120) = true := by quickRfl

end CFSG.KD.F4

namespace CFSG.KD.F5

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 128) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 14) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 56) (nat_lit 56) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 56) = true := by quickRfl

end CFSG.KD.F5

namespace CFSG.KD.F6

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 64) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 12) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 27) (nat_lit 27) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 27) = true := by quickRfl

end CFSG.KD.F6

namespace CFSG.KD.F7

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 32) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 10) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 10) (nat_lit 10) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 10) = true := by quickRfl

end CFSG.KD.F7

namespace CFSG.KD.F8

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 32) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 8) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 8) (nat_lit 8) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 8) = true := by quickRfl

end CFSG.KD.F8

namespace CFSG.KD.F9

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 16) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 6) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 4) (nat_lit 4) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 4) = true := by quickRfl

end CFSG.KD.F9

namespace CFSG.KD.F10

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 4) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 4) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 3) (nat_lit 3) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 3) = true := by quickRfl

end CFSG.KD.F10

namespace CFSG.KD.F11

theorem sH0 : wordsOK selWT selRT selST INV INV8 (nat_lit 2) HS = true := by quickRfl
theorem sH1 : invOK INV INV8 (nat_lit 2) = true := by quickRfl
theorem sH2 : aliveOK LVs (nat_lit 1) (nat_lit 2) (nat_lit 2) = true := by quickRfl
theorem sH3 : Nat.beq nC (nat_lit 2) = true := by quickRfl

end CFSG.KD.F11

end
