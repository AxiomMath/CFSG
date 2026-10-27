module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdLy

open CFSG.KC.Ord

theorem o7 : primeOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE 0x152a 0x14ee 7 = true := by
  quickRfl

theorem o11 : primeOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE 0x152a 0x14fd 11 = true := by
  quickRfl

theorem o31 : primeOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE 0x152a 0x150a 31 = true := by
  quickRfl

theorem o37 : primeOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE 0x152a 0x1521 37 = true := by
  quickRfl

theorem o67 : primeOK RW (mulR 5 12 0x534 0x6f 8 L H CM RM) ONE 0x152a 0x1529 67 = true := by
  quickRfl

theorem lcm : Nat.beq (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul 1
    (Nat.pow 2 8)) (Nat.pow 3 7)) (Nat.pow 5 6)) 7) 11) 31) 37) 67) 0xb7e827f2449700 = true := by
  quickRfl

end CFSG.KD.OrdLy

end
