module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.OkT
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.CJSuz2T

theorem okW_2 : ∀ t < 256, okW (512 + t) = true := by
  kc_cover 1

end CFSG.KD.CJSuz2T

end
