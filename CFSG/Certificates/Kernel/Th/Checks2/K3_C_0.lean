module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K3_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThK3.C_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_0_J.bin" 2166326 5694809845203631369
#kc_repo #kc_items_root CFSG.KD.ThK3.C_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_0_lo.bin" 436 9499957267848589913
#kc_repo #kc_items_root CFSG.KD.ThK3.C_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_0_acc.bin" 465 2385903504622619668

namespace CFSG.KD.ThK3.C_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runCover CFSG.KD.ThK3.blk CFSG.KD.ThK3.LVs (nat_lit 551839) (nat_lit 14)
      (CFSG.KC.LceSeg.seg CFSG.KD.ThK3.C_0.J (CFSG.KD.ThK3.C_0.lo (i + 1) - CFSG.KD.ThK3.C_0.lo i)
      (CFSG.KD.ThK3.C_0.lo i)) (CFSG.KD.ThK3.C_0.acc i)) (CFSG.KD.ThK3.C_0.acc (i + 1))

end CFSG.KD.ThK3.C_0

#kc_each_unfold CFSG.KD.ThK3.C_0.ok 0 74 as CFSG.KD.ThK3.sC
  eval CFSG.KD.ThK3.C_0.lo CFSG.KD.ThK3.C_0.acc

end
