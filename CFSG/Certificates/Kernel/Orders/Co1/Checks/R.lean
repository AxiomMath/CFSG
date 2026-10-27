module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co1.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Co1.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdCo1

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 45 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 8 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 2 6 0x90 0x18 4 L H CM RM) rels 8 ONE r

end CFSG.KD.OrdCo1

#kc_each CFSG.KD.OrdCo1.relC 0 45

namespace CFSG.KD.OrdCo1

#kc_forall_chunks R.all (fun r => relC r = true) 45 CFSG.KD.OrdCo1.relC 1

end CFSG.KD.OrdCo1

end
