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

#kc_repo #kc_items_root CFSG.KD.ThB.C_3.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_3_J.bin" 105120 15516594236235513126
#kc_repo #kc_items_root CFSG.KD.ThB.C_3.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_3_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.ThB.C_3.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_3_acc.bin" 147 4557487240454130902

namespace CFSG.KD.ThB.C_3

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runCover CFSG.KD.ThB.FB CFSG.KD.ThB.OB (nat_lit 5) (nat_lit 1184)
      CFSG.KD.ThB.osh CFSG.KD.ThB.owd CFSG.KD.ThB.om CFSG.KD.ThB.NB CFSG.KD.ThB.sel CFSG.KD.ThB.NF
      CFSG.KD.ThB.NO CFSG.KD.ThB.AL (CFSG.KC.LceSeg.seg CFSG.KD.ThB.C_3.J (CFSG.KD.ThB.C_3.lo (i + 1
      - 60) - CFSG.KD.ThB.C_3.lo (i - 60)) (CFSG.KD.ThB.C_3.lo (i - 60))) (CFSG.KD.ThB.C_3.acc (i -
      60))) (CFSG.KD.ThB.C_3.acc (i + 1 - 60))

end CFSG.KD.ThB.C_3

#kc_each_unfold CFSG.KD.ThB.C_3.ok 60 80 as CFSG.KD.ThB.c
  eval CFSG.KD.ThB.C_3.lo CFSG.KD.ThB.C_3.acc

end
