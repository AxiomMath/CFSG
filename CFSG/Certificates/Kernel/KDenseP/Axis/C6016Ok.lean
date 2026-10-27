module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6016
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6016

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6016) (nat_lit 372) = true := by
  quickRfl

end CFSG.KD.AX.c6016

end
