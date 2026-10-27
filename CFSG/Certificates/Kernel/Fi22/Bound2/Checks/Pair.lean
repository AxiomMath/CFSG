module

import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
import CFSG.Certificates.Kernel.Fi22.Bound2.Pair
import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Fi22.Bound.Data.O

#kc_repo #kc_items_root CFSG.KD.Fi22KM.PairRows.P "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/Pair_0_P.bin" 7777 18042675650864708467

namespace CFSG.KD.Fi22KM.PairRows

open CFSG.KD.Fi22KM

noncomputable def pr (g : Nat) : Bool :=
  CFSG.KC.Fi22K.pairOK CFSG.KD.Fi22BP.blk (P (12 * g + 0)) CFSG.KD.Fi22BO.UW0 CFSG.KD.Fi22BO.UW1
    (XRs (P (12 * g + 1))) (P (12 * g + 2)) (P (12 * g + 3)) (P (12 * g + 4)) (P (12 * g + 5))
    (P (12 * g + 6)) (P (12 * g + 7)) (P (12 * g + 8)) (P (12 * g + 9)) (P (12 * g + 10))
    (P (12 * g + 11))

end CFSG.KD.Fi22KM.PairRows

#kc_each_unfold CFSG.KD.Fi22KM.PairRows.pr 0 27 as CFSG.KD.Fi22KM.pr eval CFSG.KD.Fi22KM.PairRows.P
