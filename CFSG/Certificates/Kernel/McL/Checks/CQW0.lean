module

public import CFSG.Certificates.Kernel.McL.Data.CQ_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.McL.CQ

theorem okW_0 : ∀ t < 256, okW t = true := by
  kc_cover 1

end CFSG.KD.McL.CQ

end
