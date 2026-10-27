module

public import CFSG.Certificates.Kernel.Co1.Data.C1_Ok
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.C1

theorem okC_all : ∀ t < 197, okC t = true := by
  kc_cover 1

end CFSG.KD.C1

end
