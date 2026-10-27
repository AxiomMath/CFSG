module

public import CFSG.Certificates.Kernel.Co1.Data.C1_Ok
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.C1

theorem okW_0 : ∀ t < 256, okW t = true := by
  kc_cover 1

end CFSG.KD.C1

end
