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

#kc_repo #kc_items_root CFSG.KD.ThA.C_5.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_5_J.bin" 10560 8179973998107135353
#kc_repo #kc_items_root CFSG.KD.ThA.C_5.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_5_lo.bin" 54 6718073966312452302
#kc_repo #kc_items_root CFSG.KD.ThA.C_5.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_5_acc.bin" 77 6012382910261619542

namespace CFSG.KD.ThA.C_5

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runCover CFSG.KD.ThA.FB CFSG.KD.ThA.OB (nat_lit 4) (nat_lit 2336)
      CFSG.KD.ThA.osh CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.NF
      CFSG.KD.ThA.NO CFSG.KD.ThA.AL (CFSG.KC.LceSeg.seg CFSG.KD.ThA.C_5.J (CFSG.KD.ThA.C_5.lo (i + 1
      - 50) - CFSG.KD.ThA.C_5.lo (i - 50)) (CFSG.KD.ThA.C_5.lo (i - 50))) (CFSG.KD.ThA.C_5.acc (i -
      50))) (CFSG.KD.ThA.C_5.acc (i + 1 - 50))

end CFSG.KD.ThA.C_5

#kc_each_unfold CFSG.KD.ThA.C_5.ok 50 60 as CFSG.KD.ThA.c
  eval CFSG.KD.ThA.C_5.lo CFSG.KD.ThA.C_5.acc

end
