module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co3.Data.Sel
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_natLines CFSG.KD.OrdCo3 SW "CFSG/Certificates/Kernel/Orders/Co3/Checks/data/slp.txt" 1612 12941746291327882104

#kc_select CFSG.KD.OrdCo3 SWs SW.n 3

public noncomputable section

namespace CFSG.KD.OrdCo3

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM 2 0xb58 L H) 1 8 = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR 2 6 0x84 0x16 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xb58 L H) 7 ONE = true := by
  quickRfl

theorem hcnt : Nat.ble 0xe 0x73 = true := by quickRfl

theorem hAB : CFSG.KC.Ord.andB
    (CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 0x38 0x74) (CFSG.KC.Ord.regBelow 0x73 0x74))
    (CFSG.KC.Ord.andB (Nat.beq (RH 0x38) (RW 1)) (Nat.beq (RH 0x73) (RW 2))) = true := by
  quickRfl

@[expose] def hsSt (k : Nat) : Nat := Nat.min (8 + 48 * k) 116

@[expose] def hsC (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR 2 6 0x84 0x16 4 L H CM RM)
    (CFSG.KC.Ord.validM 2 0xb58 L H) ONE [SWs k] (hsSt k)) (hsSt (k + 1))

end CFSG.KD.OrdCo3

#kc_each CFSG.KD.OrdCo3.hsC 0 3

namespace CFSG.KD.OrdCo3

#kc_forall_chunks SG.all (fun k => hsC k = true) 3 CFSG.KD.OrdCo3.hsC 1

end CFSG.KD.OrdCo3

end
