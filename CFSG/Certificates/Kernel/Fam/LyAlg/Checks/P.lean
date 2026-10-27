module

public import CFSG.Certificates.Kernel.Orders.Cert
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.LyAlg.Data.Sel

public section

namespace CFSG.KD.FamLyAlg

open CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat := mulR 5 12 1332 111 8 L H CM RM

theorem p_5 : Nat.beq (RW 5) (mul (RW 2) (RW 1)) = true := by quickRfl

theorem p_6 : Nat.beq (RW 6) (mul (RW 5) (RW 2)) = true := by quickRfl

theorem p_7 : Nat.beq (RW 7) (mul (RW 6) (RW 1)) = true := by quickRfl

theorem p_8 : Nat.beq (RW 8) (mul (RW 2) (RW 1)) = true := by quickRfl

theorem p_9 : Nat.beq (RW 9) (mul (RW 1) (RW 2)) = true := by quickRfl

theorem p_10 : Nat.beq (RW 10) (mul (RW 9) (RW 2)) = true := by quickRfl

theorem p_11 : Nat.beq (RW 11) (mul (RW 10) (RW 1)) = true := by quickRfl

theorem p_12 : Nat.beq (RW 12) (mul (RW 2) (RW 2)) = true := by quickRfl

end CFSG.KD.FamLyAlg

end
