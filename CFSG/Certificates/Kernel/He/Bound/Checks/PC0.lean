module

public import CFSG.Certificates.Kernel.He.Bound.Data.P_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.HeBP

theorem okC_0 : ∀ t < 256, okC t = true := by
  kc_cover 1

end CFSG.KD.HeBP

end
