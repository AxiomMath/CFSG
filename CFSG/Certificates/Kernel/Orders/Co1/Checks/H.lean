module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co1.Data.Sel
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_natLines CFSG.KD.OrdCo1 SW "CFSG/Certificates/Kernel/Orders/Co1/Checks/data/slp.txt" 20831 16803799668516983437

#kc_select CFSG.KD.OrdCo1 SWs SW.n 29

public noncomputable section

namespace CFSG.KD.OrdCo1

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM 2 0xd80 L H) 1 9 = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR 2 6 0x90 0x18 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xd80 L H) 8 ONE = true := by
  quickRfl

theorem hcnt : Nat.ble 0x10 0x576 = true := by quickRfl

theorem hAB : CFSG.KC.Ord.andB
    (CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 0x14a 0x577) (CFSG.KC.Ord.regBelow 0x576 0x577))
    (CFSG.KC.Ord.andB (Nat.beq (RH 0x14a) (RW 1)) (Nat.beq (RH 0x576) (RW 2))) = true := by
  quickRfl

@[expose] def hsSt (k : Nat) : Nat := Nat.min (9 + 48 * k) 1399

@[expose] def hsC (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR 2 6 0x90 0x18 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xd80 L H) ONE [SWs k] (hsSt k)) (hsSt (k + 1))

end CFSG.KD.OrdCo1

#kc_each CFSG.KD.OrdCo1.hsC 0 29

namespace CFSG.KD.OrdCo1

#kc_forall_chunks SG.all (fun k => hsC k = true) 29 CFSG.KD.OrdCo1.hsC 1

end CFSG.KD.OrdCo1

end
