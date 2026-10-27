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

#kc_repo #kc_items_root CFSG.KD.ThB.W_13.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_13_J.bin" 407096 12388913634679705166
#kc_repo #kc_items_root CFSG.KD.ThB.W_13.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_13_lo.bin" 267 17091675366452044911
#kc_repo #kc_items_root CFSG.KD.ThB.W_13.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_13_acc.bin" 432 13953356967688815870

namespace CFSG.KD.ThB.W_13

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThB.FB CFSG.KD.ThB.HB CFSG.KD.ThB.GB CFSG.KD.ThB.TB
      CFSG.KD.ThB.WD (nat_lit 5) (nat_lit 1184) CFSG.KD.ThB.LT CFSG.KD.ThB.TL CFSG.KD.ThB.VL
      CFSG.KD.ThB.NL CFSG.KD.ThB.ND CFSG.KD.ThB.NO CFSG.KD.ThB.nH CFSG.KD.ThB.nT CFSG.KD.ThB.nW
      CFSG.KD.ThB.W CFSG.KD.ThB.Wi false (CFSG.KC.LceSeg.seg CFSG.KD.ThB.W_13.J (CFSG.KD.ThB.W_13.lo
      (i + 1 - 620) - CFSG.KD.ThB.W_13.lo (i - 620)) (CFSG.KD.ThB.W_13.lo (i - 620)))
      (CFSG.KD.ThB.W_13.acc (i - 620))) (CFSG.KD.ThB.W_13.acc (i + 1 - 620))

end CFSG.KD.ThB.W_13

#kc_each_unfold CFSG.KD.ThB.W_13.ok 620 667 as CFSG.KD.ThB.w
  eval CFSG.KD.ThB.W_13.lo CFSG.KD.ThB.W_13.acc

end
