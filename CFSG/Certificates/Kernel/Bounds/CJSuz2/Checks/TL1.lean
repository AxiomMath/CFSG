module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.OkT
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.CJSuz2T

theorem okL_1 : ∀ t < 488, okL (488 + t) = true := by
  kc_cover 1

theorem okY_all : ∀ k < 4, okY k = true := by
  kc_cover 1

end CFSG.KD.CJSuz2T

end
