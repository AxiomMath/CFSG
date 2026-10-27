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

#kc_repo #kc_items_root CFSG.KD.ThB.W_15.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_15_J.bin" 404193 261859690589467649
#kc_repo #kc_items_root CFSG.KD.ThB.W_15.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_15_lo.bin" 267 17091675366452044911
#kc_repo #kc_items_root CFSG.KD.ThB.W_15.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_15_acc.bin" 432 3331490025035364827

namespace CFSG.KD.ThB.W_15

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThB.FB CFSG.KD.ThB.HB CFSG.KD.ThB.GB CFSG.KD.ThB.TB
      CFSG.KD.ThB.WD (nat_lit 5) (nat_lit 1184) CFSG.KD.ThB.LT CFSG.KD.ThB.TL CFSG.KD.ThB.VL
      CFSG.KD.ThB.NL CFSG.KD.ThB.ND CFSG.KD.ThB.NO CFSG.KD.ThB.nH CFSG.KD.ThB.nT CFSG.KD.ThB.nW
      CFSG.KD.ThB.W CFSG.KD.ThB.Wi false (CFSG.KC.LceSeg.seg CFSG.KD.ThB.W_15.J (CFSG.KD.ThB.W_15.lo
      (i + 1 - 715) - CFSG.KD.ThB.W_15.lo (i - 715)) (CFSG.KD.ThB.W_15.lo (i - 715)))
      (CFSG.KD.ThB.W_15.acc (i - 715))) (CFSG.KD.ThB.W_15.acc (i + 1 - 715))

end CFSG.KD.ThB.W_15

#kc_each_unfold CFSG.KD.ThB.W_15.ok 715 762 as CFSG.KD.ThB.w
  eval CFSG.KD.ThB.W_15.lo CFSG.KD.ThB.W_15.acc

end
