module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.He.Data.Sel
public import CFSG.Certificates.Kernel.Orders.He.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHe

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 7 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 7 0xc 0x258 0x32 8 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdHe

#kc_each CFSG.KD.OrdHe.relC 0 7

namespace CFSG.KD.OrdHe

#kc_forall_chunks R.all (fun r => relC r = true) 7 CFSG.KD.OrdHe.relC 1

end CFSG.KD.OrdHe

end
