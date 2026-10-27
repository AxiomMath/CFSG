module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6017
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6017

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6017) (nat_lit 96) = true := by
  quickRfl

end CFSG.KD.AX.c6017

#kc_each CFSG.KD.AX.c6017.u 0 11

end
