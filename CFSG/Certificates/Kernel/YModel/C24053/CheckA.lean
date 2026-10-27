module

public import CFSG.Certificates.Kernel.YModel.C24053.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.C24053

open CFSG.KC.YModel

#kc_each x1Chk24053_ 0 104

theorem x1Neg24053 :
    (!weqK 15 10 CFSG.KD.YMY432F.Nf [0] [] &&
      !weqK 15 10 CFSG.KD.YMY432F.Nf (rel 132).dropLast [] &&
      !pairOK 22 && !pairOK 133 &&
      !decide (word 23 = invW (word 20)) && !decide (word 23 = rot1 (invW (word 20)))) = true := by
  quickRfl

end CFSG.KD.C24053

end
