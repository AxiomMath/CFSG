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

#kc_repo #kc_items_root CFSG.KD.ThB.H_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_0_J.bin" 215501 14217819971500085727
#kc_repo #kc_items_root CFSG.KD.ThB.H_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_0_lo.bin" 104 7355971307750990515
#kc_repo #kc_items_root CFSG.KD.ThB.H_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_0_acc.bin" 125 10250856434246106367

namespace CFSG.KD.ThB.H_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runHdr CFSG.KD.ThB.HB CFSG.KD.ThA.FB CFSG.KD.ThB.LT CFSG.KD.ThB.TL
      CFSG.KD.ThB.VL CFSG.KD.ThB.NL (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.NF (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.H_0.J (CFSG.KD.ThB.H_0.lo (i + 1) - CFSG.KD.ThB.H_0.lo i) (CFSG.KD.ThB.H_0.lo i))
      (CFSG.KD.ThB.H_0.acc i)) (CFSG.KD.ThB.H_0.acc (i + 1))

end CFSG.KD.ThB.H_0

#kc_each_unfold CFSG.KD.ThB.H_0.ok 0 20 as CFSG.KD.ThB.h
  eval CFSG.KD.ThB.H_0.lo CFSG.KD.ThB.H_0.acc

end
