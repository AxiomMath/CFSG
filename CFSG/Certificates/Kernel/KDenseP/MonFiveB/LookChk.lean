module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look

public section

namespace CFSG.KD.M5BL

open CFSG.KC CFSG.KC.KDenseP

theorem tab_ok : tabChk CT SC PI (nat_lit 561) CFSG.KD.M5BM.MT.keys (nat_lit 0) = true := by
  decide +kernel

theorem len_ok : 561 ≤ CFSG.KD.M5BM.MT.keys.length := by decide +kernel

end CFSG.KD.M5BL

end
