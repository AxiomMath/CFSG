module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.C6085W
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 200000

namespace CFSG.KD.TP.c6085

@[expose] noncomputable def u (g : Nat) : Bool :=
  CFSG.KC.KDenseP.grpL rn
    (CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.TPM.MT WL)
    CH PRf Gf S0 (nat_lit 21) g

end CFSG.KD.TP.c6085

#kc_each CFSG.KD.TP.c6085.u 0 25

end
