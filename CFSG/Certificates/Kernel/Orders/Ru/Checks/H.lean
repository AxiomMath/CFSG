module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Sel
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_natLines CFSG.KD.OrdRu SW "CFSG/Certificates/Kernel/Orders/Ru/Checks/data/slp.txt" 4465 14767837247149067434

#kc_select CFSG.KD.OrdRu SWs SW.n 7

public noncomputable section

namespace CFSG.KD.OrdRu

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM 2 0x1260 L H) 1 4 = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR 2 6 0xa8 0x1c 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0x1260 L H) 3 ONE = true := by
  quickRfl

theorem hcnt : Nat.ble 6 0x12e = true := by quickRfl

theorem hAB : CFSG.KC.Ord.andB
    (CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 0xed 0x12f) (CFSG.KC.Ord.regBelow 0x12e 0x12f))
    (CFSG.KC.Ord.andB (Nat.beq (RH 0xed) (RW 1)) (Nat.beq (RH 0x12e) (RW 2))) = true := by
  quickRfl

@[expose] def hsSt (k : Nat) : Nat := Nat.min (4 + 48 * k) 303

@[expose] def hsC (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR 2 6 0xa8 0x1c 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0x1260 L H) ONE [SWs k] (hsSt k)) (hsSt (k + 1))

end CFSG.KD.OrdRu

#kc_each CFSG.KD.OrdRu.hsC 0 7

namespace CFSG.KD.OrdRu

#kc_forall_chunks SG.all (fun k => hsC k = true) 7 CFSG.KD.OrdRu.hsC 1

end CFSG.KD.OrdRu

end
