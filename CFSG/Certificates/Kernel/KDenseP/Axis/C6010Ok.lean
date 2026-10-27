module

public import CFSG.Certificates.Kernel.KDenseP.Axis.C6010
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 200000

namespace CFSG.KD.AX.c6010

theorem weq : CFSG.KC.KDenseP.wordsEqB WD
    (CFSG.KC.KDense.Y443.words CFSG.KC.KDenseP.Axis.p6010) (nat_lit 516) = true := by
  quickRfl

end CFSG.KD.AX.c6010

end
