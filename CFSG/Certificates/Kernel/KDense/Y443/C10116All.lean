
module

public import CFSG.Certificates.Kernel.KDense.Y443.C10116
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Y443.c10116

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDense.chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDense.Y443.p10116) S (CH k)

end CFSG.KD.Y443.c10116

#kc_each CFSG.KD.Y443.c10116.t 0 126

end
