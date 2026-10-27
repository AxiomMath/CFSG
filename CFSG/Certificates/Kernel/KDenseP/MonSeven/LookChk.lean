module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look

public section

namespace CFSG.KD.M7L

open CFSG.KC CFSG.KC.KDenseP

theorem tab_ok : tabChk CT SC PI (nat_lit 638) CFSG.KD.M7M.MT.keys (nat_lit 0) = true := by
  decide +kernel

theorem len_ok : 638 ≤ CFSG.KD.M7M.MT.keys.length := by decide +kernel

end CFSG.KD.M7L

end
