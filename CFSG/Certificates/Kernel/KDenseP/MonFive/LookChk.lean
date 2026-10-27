module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Look

public section

namespace CFSG.KD.M5RL

open CFSG.KC CFSG.KC.KDenseP

theorem tab_ok : tabChk CT SC PI (nat_lit 1488) CFSG.KD.M5RM.MT.keys (nat_lit 0) = true := by
  decide +kernel

theorem len_ok : 1488 ≤ CFSG.KD.M5RM.MT.keys.length := by decide +kernel

end CFSG.KD.M5RL

end
