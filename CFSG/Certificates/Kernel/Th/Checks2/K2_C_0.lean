module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K2_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThK2.C_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_C_0_J.bin" 844717 10368059770768501716
#kc_repo #kc_items_root CFSG.KD.ThK2.C_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_C_0_lo.bin" 170 3089030601822650425
#kc_repo #kc_items_root CFSG.KD.ThK2.C_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_C_0_acc.bin" 179 719772390967649797

namespace CFSG.KD.ThK2.C_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runCover CFSG.KD.ThK2.blk CFSG.KD.ThK2.LVs (nat_lit 173901) (nat_lit 12)
      (CFSG.KC.LceSeg.seg CFSG.KD.ThK2.C_0.J (CFSG.KD.ThK2.C_0.lo (i + 1) - CFSG.KD.ThK2.C_0.lo i)
      (CFSG.KD.ThK2.C_0.lo i)) (CFSG.KD.ThK2.C_0.acc i)) (CFSG.KD.ThK2.C_0.acc (i + 1))

end CFSG.KD.ThK2.C_0

#kc_each_unfold CFSG.KD.ThK2.C_0.ok 0 29 as CFSG.KD.ThK2.sC
  eval CFSG.KD.ThK2.C_0.lo CFSG.KD.ThK2.C_0.acc

end
