module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J3.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ3

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM 2 0xc800 L H) 1 3 = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR 2 8 0x280 0x50 6 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xc800 L H) 2 ONE = true := by
  quickRfl

theorem hcnt : Nat.ble 4 4 = true := by quickRfl

theorem hAB : CFSG.KC.Ord.andB
    (CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 1 5) (CFSG.KC.Ord.regBelow 2 5))
    (CFSG.KC.Ord.andB (Nat.beq (RH 1) (RW 1)) (Nat.beq (RH 2) (RW 2))) = true := by
  quickRfl

theorem hs_0 : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR 2 8 0x280 0x50 6 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xc800 L H) ONE [0x2800000000000602] 3) 5 = true := by
  quickRfl

end CFSG.KD.OrdJ3

end
