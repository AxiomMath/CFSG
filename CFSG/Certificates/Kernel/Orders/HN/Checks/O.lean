module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHN

open CFSG.KC.Ord

theorem o7 : primeOK RW (mulR 5 13 0x6c1 0x85 9 L H CM RM) ONE 799 0x2ea 7 = true := by quickRfl

theorem o11 : primeOK RW (mulR 5 13 0x6c1 0x85 9 L H CM RM) ONE 799 0x2ed 11 = true := by quickRfl

theorem o19 : primeOK RW (mulR 5 13 0x6c1 0x85 9 L H CM RM) ONE 799 0x31e 19 = true := by quickRfl

theorem lcm : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul 1 (Nat.pow 2 14))
    (Nat.pow 3 6)) (Nat.pow 5 6)) 7) 11) 19) 0xf851f685c000 = true := by
  quickRfl

end CFSG.KD.OrdHN

end
