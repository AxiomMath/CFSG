module

public import CFSG.Certificates.Kernel.Orders.Cert
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel

public section

namespace CFSG.KD.FamHNSeed

open CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat := mulR 5 13 1729 133 9 L H CM RM

theorem g_inv : Nat.beq (mul (RW 16) (RW 17)) ONE = true := by quickRfl

theorem x_18 : Nat.beq (RW 18) (mul (RW 1) (RW 17)) = true := by quickRfl

theorem x_19 : Nat.beq (RW 19) (mul (RW 18) (RW 2)) = true := by quickRfl

theorem x_20 : Nat.beq (RW 20) (mul (RW 19) (RW 16)) = true := by quickRfl

end CFSG.KD.FamHNSeed

end
