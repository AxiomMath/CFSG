
module

public import CFSG.Certificates.Kernel.KDense.Y443.C10124
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Y443.c10124

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDense.chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDense.Y443.pSwap) S (CH k)

end CFSG.KD.Y443.c10124

#kc_each CFSG.KD.Y443.c10124.t 0 10

end
