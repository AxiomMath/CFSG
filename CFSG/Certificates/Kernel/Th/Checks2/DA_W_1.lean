module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThA.W_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_1_J.bin" 380988 6117083046876234446
#kc_repo #kc_items_root CFSG.KD.ThA.W_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_1_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.ThA.W_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_1_acc.bin" 441 14169470306491019146

namespace CFSG.KD.ThA.W_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThA.FB CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.TB
      CFSG.KD.ThA.WD (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.LT CFSG.KD.ThA.TL CFSG.KD.ThA.VL
      CFSG.KD.ThA.NL CFSG.KD.ThA.ND CFSG.KD.ThA.NO CFSG.KD.ThA.nH CFSG.KD.ThA.nT CFSG.KD.ThA.nW
      CFSG.KD.ThA.W CFSG.KD.ThA.Wi true (CFSG.KC.LceSeg.seg CFSG.KD.ThA.W_1.J (CFSG.KD.ThA.W_1.lo (i
      + 1 - 48) - CFSG.KD.ThA.W_1.lo (i - 48)) (CFSG.KD.ThA.W_1.lo (i - 48))) (CFSG.KD.ThA.W_1.acc
      (i - 48))) (CFSG.KD.ThA.W_1.acc (i + 1 - 48))

end CFSG.KD.ThA.W_1

#kc_each_unfold CFSG.KD.ThA.W_1.ok 48 96 as CFSG.KD.ThA.w
  eval CFSG.KD.ThA.W_1.lo CFSG.KD.ThA.W_1.acc

end
