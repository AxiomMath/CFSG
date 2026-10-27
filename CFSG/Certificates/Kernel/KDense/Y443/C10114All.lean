
module

public import CFSG.Certificates.Kernel.KDense.Y443.C10114
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Y443.c10114

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDense.chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDense.Y443.pCover) S (CH k)

end CFSG.KD.Y443.c10114

#kc_each CFSG.KD.Y443.c10114.t 0 29

end
