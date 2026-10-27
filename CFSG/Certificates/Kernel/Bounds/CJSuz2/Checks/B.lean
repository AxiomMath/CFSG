module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.OkB
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.CJSuz2B

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.CJSuz2B

end
