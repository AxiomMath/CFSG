module

public import CFSG.Certificates.Kernel.Co1.Data.C2_Ok
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.C2

theorem okW_1 : ∀ t < 256, okW (256 + t) = true := by
  kc_cover 1

end CFSG.KD.C2

end
