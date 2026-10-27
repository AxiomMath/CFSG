module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6018
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6018

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6018) (nat_lit 144) = true := by
  quickRfl

end CFSG.KD.AX.c6018

#kc_each CFSG.KD.AX.c6018.u 0 11

end
