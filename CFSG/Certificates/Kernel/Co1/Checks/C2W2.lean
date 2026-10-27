module

public import CFSG.Certificates.Kernel.Co1.Data.C2_Ok
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.C2

theorem okW_2 : ∀ t < 108, okW (512 + t) = true := by
  kc_cover 1

end CFSG.KD.C2

end
