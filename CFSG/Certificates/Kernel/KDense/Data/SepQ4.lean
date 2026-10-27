module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem q4 : qOK U MK (nat_lit 4) (QSf (nat_lit 4)) = true := by quickRfl

end CFSG.KD.KDS

end
