module

public import CFSG.Certificates.Kernel.He.Bound.Data.P_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.HeBP

theorem okW_4 : ∀ t < 107, okW (1024 + t) = true := by
  kc_cover 1

end CFSG.KD.HeBP

end
