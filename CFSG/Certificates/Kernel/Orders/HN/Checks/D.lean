module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHN

open CFSG.KC.Ord

theorem d1 : Nat.beq (decRun P1 256 17976 (nat_lit 5) (nat_lit 0x85) (nat_lit 13) (nat_lit 0x6c1) RM
    (RW 1) (List.range 71) 1) (nat_lit 0x11467) = true := by
  quickRfl

theorem d1_end : seedDone (nat_lit 0x85) (validM (nat_lit 5) (nat_lit 0x38245) L H) (RW 1)
    (nat_lit 0x11467) = true := by
  quickRfl

theorem d2 : Nat.beq (decRun P2 256 17976 (nat_lit 5) (nat_lit 0x85) (nat_lit 13) (nat_lit 0x6c1) RM
    (RW 2) (List.range 71) 1) (nat_lit 0x11467) = true := by
  quickRfl

theorem d2_end : seedDone (nat_lit 0x85) (validM (nat_lit 5) (nat_lit 0x38245) L H) (RW 2)
    (nat_lit 0x11467) = true := by
  quickRfl

end CFSG.KD.OrdHN

end
