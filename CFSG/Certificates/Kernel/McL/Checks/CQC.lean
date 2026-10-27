module

public import CFSG.Certificates.Kernel.McL.Data.CQ_Tab
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.McL.CQ

theorem okC_all : ∀ t < 102, okC t = true := by
  kc_cover 1

end CFSG.KD.McL.CQ

end
