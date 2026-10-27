module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HS.Data.Sel
public import CFSG.Certificates.Kernel.Orders.HS.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHS

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 13 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 2 6 0x78 0x14 4 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdHS

#kc_each CFSG.KD.OrdHS.relC 0 13

namespace CFSG.KD.OrdHS

#kc_forall_chunks R.all (fun r => relC r = true) 13 CFSG.KD.OrdHS.relC 1

end CFSG.KD.OrdHS

end
