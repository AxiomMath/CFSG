module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThB.H_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_1_J.bin" 215784 17975007969539308230
#kc_repo #kc_items_root CFSG.KD.ThB.H_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_1_lo.bin" 104 7355971307750990515
#kc_repo #kc_items_root CFSG.KD.ThB.H_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_1_acc.bin" 134 5493149110401514923

namespace CFSG.KD.ThB.H_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runHdr CFSG.KD.ThB.HB CFSG.KD.ThA.FB CFSG.KD.ThB.LT CFSG.KD.ThB.TL
      CFSG.KD.ThB.VL CFSG.KD.ThB.NL (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.NF (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.H_1.J (CFSG.KD.ThB.H_1.lo (i + 1 - 20) - CFSG.KD.ThB.H_1.lo (i - 20))
      (CFSG.KD.ThB.H_1.lo (i - 20))) (CFSG.KD.ThB.H_1.acc (i - 20))) (CFSG.KD.ThB.H_1.acc (i + 1 -
      20))

end CFSG.KD.ThB.H_1

#kc_each_unfold CFSG.KD.ThB.H_1.ok 20 40 as CFSG.KD.ThB.h
  eval CFSG.KD.ThB.H_1.lo CFSG.KD.ThB.H_1.acc

end
