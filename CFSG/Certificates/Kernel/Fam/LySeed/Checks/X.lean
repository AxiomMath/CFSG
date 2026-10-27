module

public import CFSG.Certificates.Kernel.Orders.Cert
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel

public section

namespace CFSG.KD.FamLySeed

open CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat := mulR 5 12 1332 111 8 L H CM RM

theorem g_inv : Nat.beq (mul (RW 14) (RW 15)) ONE = true := by quickRfl

theorem x_16 : Nat.beq (RW 16) (mul (RW 1) (RW 15)) = true := by quickRfl

theorem x_17 : Nat.beq (RW 17) (mul (RW 16) (RW 2)) = true := by quickRfl

theorem x_18 : Nat.beq (RW 18) (mul (RW 17) (RW 14)) = true := by quickRfl

end CFSG.KD.FamLySeed

end
