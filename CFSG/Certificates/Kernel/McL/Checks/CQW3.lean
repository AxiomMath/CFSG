module

public import CFSG.Certificates.Kernel.McL.Data.CQ_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.McL.CQ

theorem okW_3 : ∀ t < 105, okW (768 + t) = true := by
  kc_cover 1

end CFSG.KD.McL.CQ

end
