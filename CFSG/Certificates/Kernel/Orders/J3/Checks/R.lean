module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J3.Data.Sel
public import CFSG.Certificates.Kernel.Orders.J3.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ3

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 8 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 2 8 0x280 0x50 6 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdJ3

#kc_each CFSG.KD.OrdJ3.relC 0 8

namespace CFSG.KD.OrdJ3

#kc_forall_chunks R.all (fun r => relC r = true) 8 CFSG.KD.OrdJ3.relC 1

end CFSG.KD.OrdJ3

end
