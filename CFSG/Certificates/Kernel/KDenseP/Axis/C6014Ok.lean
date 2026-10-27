module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6014
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6014

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6014) (nat_lit 384) = true := by
  quickRfl

end CFSG.KD.AX.c6014

end
