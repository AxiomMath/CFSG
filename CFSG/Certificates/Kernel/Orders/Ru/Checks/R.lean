module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Ru.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdRu

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 12 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 3 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 2 6 0xa8 0x1c 4 L H CM RM) rels 3 ONE r

end CFSG.KD.OrdRu

#kc_each CFSG.KD.OrdRu.relC 0 12

namespace CFSG.KD.OrdRu

#kc_forall_chunks R.all (fun r => relC r = true) 12 CFSG.KD.OrdRu.relC 1

end CFSG.KD.OrdRu

end
