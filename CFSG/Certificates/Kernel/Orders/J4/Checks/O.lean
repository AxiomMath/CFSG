module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ4

open CFSG.KC.Ord

theorem o5 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xdb8 5 = true := by quickRfl

theorem o7 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xdd0 7 = true := by quickRfl

theorem o23 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xde3 23 = true := by quickRfl

theorem o29 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xdff 29 = true := by quickRfl

theorem o31 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xe10 31 = true := by quickRfl

theorem o37 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xe13 37 = true := by quickRfl

theorem o43 : primeOK RW (mulR 2 8 0x380 0x70 6 L H CM RM) ONE 0xe27 0xe26 43 = true := by quickRfl

theorem lcm : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul
    (Nat.mul (Nat.mul 1 (Nat.pow 2 21)) (Nat.pow 3 3)) (Nat.pow 11 3)) 5) 7) 23) 29) 31) 37) 43)
    0x4b440c21c17200000 = true := by
  quickRfl

end CFSG.KD.OrdJ4

end
