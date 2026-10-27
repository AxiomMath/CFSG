module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co2.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Co2.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdCo2

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 10 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 2 6 0x84 0x16 4 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdCo2

#kc_each CFSG.KD.OrdCo2.relC 0 10

namespace CFSG.KD.OrdCo2

#kc_forall_chunks R.all (fun r => relC r = true) 10 CFSG.KD.OrdCo2.relC 1

end CFSG.KD.OrdCo2

end
