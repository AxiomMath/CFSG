module

import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M
import CFSG.Certificates.Kernel.Bounds.HSAlt.Pair
import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.B_Sel

#kc_repo #kc_items_root CFSG.KD.HSKM.PairRows.P "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/M/rows/Pair_0_P.bin" 29446 14591379525683841840

namespace CFSG.KD.HSKM.PairRows

open CFSG.KD.HSKM

noncomputable def pr (g : Nat) : Bool :=
  CFSG.KC.HSK.pairOK CFSG.KD.HSKB.blk CFSG.KC.HSK.gen CFSG.KC.HSK.subB (P (13 * g + 0))
    (P (13 * g + 1)) (XRs (P (13 * g + 2))) (P (13 * g + 3)) (P (13 * g + 4)) (P (13 * g + 5))
    (P (13 * g + 6)) (P (13 * g + 7)) (P (13 * g + 8)) (P (13 * g + 9)) (P (13 * g + 10))
    (P (13 * g + 11)) (P (13 * g + 12))

end CFSG.KD.HSKM.PairRows

#kc_each_unfold CFSG.KD.HSKM.PairRows.pr 0 87 as CFSG.KD.HSKM.pr eval CFSG.KD.HSKM.PairRows.P
