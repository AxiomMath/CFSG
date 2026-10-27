module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.McL.Data.Sel
public import CFSG.Certificates.Kernel.Orders.McL.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdMcL

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 15 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 3 8 0xa8 0x15 5 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdMcL

#kc_each CFSG.KD.OrdMcL.relC 0 15

namespace CFSG.KD.OrdMcL

#kc_forall_chunks R.all (fun r => relC r = true) 15 CFSG.KD.OrdMcL.relC 1

end CFSG.KD.OrdMcL

end
