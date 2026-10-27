module

public import CFSG.Certificates.Kernel.He.Bound.Data.P_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.HeBP

theorem okW_2 : ∀ t < 256, okW (512 + t) = true := by
  kc_cover 1

end CFSG.KD.HeBP

end
