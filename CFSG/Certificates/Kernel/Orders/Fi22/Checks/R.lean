module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Fi22.Data.Sel
public import CFSG.Certificates.Kernel.Orders.Fi22.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdFi22

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels rels) 13 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded rels 2 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 3 0xa 0x302 0x4d 7 L H CM RM) rels 2 ONE r

end CFSG.KD.OrdFi22

#kc_each CFSG.KD.OrdFi22.relC 0 13

namespace CFSG.KD.OrdFi22

#kc_forall_chunks R.all (fun r => relC r = true) 13 CFSG.KD.OrdFi22.relC 1

end CFSG.KD.OrdFi22

end
