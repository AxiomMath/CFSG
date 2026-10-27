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

#kc_repo #kc_items_root CFSG.KD.ThK3.C_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_1_J.bin" 785711 16989241730301716340
#kc_repo #kc_items_root CFSG.KD.ThK3.C_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_1_lo.bin" 140 5071780118024691062
#kc_repo #kc_items_root CFSG.KD.ThK3.C_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_C_1_acc.bin" 182 16397141440742869797

namespace CFSG.KD.ThK3.C_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runCover CFSG.KD.ThK3.blk CFSG.KD.ThK3.LVs (nat_lit 551839) (nat_lit 14)
      (CFSG.KC.LceSeg.seg CFSG.KD.ThK3.C_1.J (CFSG.KD.ThK3.C_1.lo (i + 1 - 74) - CFSG.KD.ThK3.C_1.lo
      (i - 74)) (CFSG.KD.ThK3.C_1.lo (i - 74))) (CFSG.KD.ThK3.C_1.acc (i - 74)))
      (CFSG.KD.ThK3.C_1.acc (i + 1 - 74))

end CFSG.KD.ThK3.C_1

#kc_each_unfold CFSG.KD.ThK3.C_1.ok 74 99 as CFSG.KD.ThK3.sC
  eval CFSG.KD.ThK3.C_1.lo CFSG.KD.ThK3.C_1.acc

end
