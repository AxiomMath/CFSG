module

import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Co2.Bound3.Data.M
import CFSG.Certificates.Kernel.Co2.Bound3.Pair
import CFSG.Certificates.Kernel.Co2.Bound3.Rels
import CFSG.Certificates.Kernel.Co2.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Co2.Bound.Data.O

#kc_repo #kc_items_root CFSG.KD.Co2KM.PairRows.P "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/Pair_0_P.bin" 4245 11362923807192574844

namespace CFSG.KD.Co2KM.PairRows

open CFSG.KD.Co2KM

noncomputable def pr (g : Nat) : Bool :=
  CFSG.KC.Co2K.pairOK CFSG.KD.Co2BP.blk CFSG.KC.Co2K.gen (P (12 * g + 0)) CFSG.KD.Co2BO.UW0
    CFSG.KD.Co2BO.UW1 CFSG.KD.Co2BO.UW2 CFSG.KD.Co2BO.UW3 (XRs (P (12 * g + 1))) (P (12 * g + 2))
    (P (12 * g + 3)) (P (12 * g + 4)) (P (12 * g + 5)) (P (12 * g + 6)) (P (12 * g + 7))
    (P (12 * g + 8)) (P (12 * g + 9)) (P (12 * g + 10)) (P (12 * g + 11))

end CFSG.KD.Co2KM.PairRows

#kc_each_unfold CFSG.KD.Co2KM.PairRows.pr 0 23 as CFSG.KD.Co2KM.pr eval CFSG.KD.Co2KM.PairRows.P
