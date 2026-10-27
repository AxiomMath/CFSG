module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
public import CFSG.Certificates.Kernel.Fam.J4.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamJ4

theorem rinv : CFSG.KC.Fam.invPairs RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn
    0x23001a0016 0x2600250024 3 = true := by
  quickRfl

theorem rlen : Nat.beq (CFSG.KC.Ord.lenRels rels) 12 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Fam.relOKL RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) rels ONE 0x23001a0016
    0x2600250024 r

end CFSG.KD.FamJ4

#kc_each CFSG.KD.FamJ4.relC 0 12

namespace CFSG.KD.FamJ4

#kc_forall_chunks R.all (fun r => relC r = true) 12 CFSG.KD.FamJ4.relC 1

end CFSG.KD.FamJ4

end
