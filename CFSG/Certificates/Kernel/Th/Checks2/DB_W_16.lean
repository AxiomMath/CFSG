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

#kc_repo #kc_items_root CFSG.KD.ThB.W_16.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_16_J.bin" 345017 4766354104671007192
#kc_repo #kc_items_root CFSG.KD.ThB.W_16.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_16_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.ThB.W_16.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_W_16_acc.bin" 441 14066973910392876140

namespace CFSG.KD.ThB.W_16

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThB.FB CFSG.KD.ThB.HB CFSG.KD.ThB.GB CFSG.KD.ThB.TB
      CFSG.KD.ThB.WD (nat_lit 5) (nat_lit 1184) CFSG.KD.ThB.LT CFSG.KD.ThB.TL CFSG.KD.ThB.VL
      CFSG.KD.ThB.NL CFSG.KD.ThB.ND CFSG.KD.ThB.NO CFSG.KD.ThB.nH CFSG.KD.ThB.nT CFSG.KD.ThB.nW
      CFSG.KD.ThB.W CFSG.KD.ThB.Wi false (CFSG.KC.LceSeg.seg CFSG.KD.ThB.W_16.J (CFSG.KD.ThB.W_16.lo
      (i + 1 - 762) - CFSG.KD.ThB.W_16.lo (i - 762)) (CFSG.KD.ThB.W_16.lo (i - 762)))
      (CFSG.KD.ThB.W_16.acc (i - 762))) (CFSG.KD.ThB.W_16.acc (i + 1 - 762))

end CFSG.KD.ThB.W_16

#kc_each_unfold CFSG.KD.ThB.W_16.ok 762 810 as CFSG.KD.ThB.w
  eval CFSG.KD.ThB.W_16.lo CFSG.KD.ThB.W_16.acc

end
