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

#kc_repo #kc_items_root CFSG.KD.ThB.C_4.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_4_J.bin" 76711 5843928243937870475
#kc_repo #kc_items_root CFSG.KD.ThB.C_4.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_4_lo.bin" 79 14753111812634269309
#kc_repo #kc_items_root CFSG.KD.ThB.C_4.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_C_4_acc.bin" 105 14974971222827812259

namespace CFSG.KD.ThB.C_4

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runCover CFSG.KD.ThB.FB CFSG.KD.ThB.OB (nat_lit 5) (nat_lit 1184)
      CFSG.KD.ThB.osh CFSG.KD.ThB.owd CFSG.KD.ThB.om CFSG.KD.ThB.NB CFSG.KD.ThB.sel CFSG.KD.ThB.NF
      CFSG.KD.ThB.NO CFSG.KD.ThB.AL (CFSG.KC.LceSeg.seg CFSG.KD.ThB.C_4.J (CFSG.KD.ThB.C_4.lo (i + 1
      - 80) - CFSG.KD.ThB.C_4.lo (i - 80)) (CFSG.KD.ThB.C_4.lo (i - 80))) (CFSG.KD.ThB.C_4.acc (i -
      80))) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThB.C_4.acc (i + 1 - 80)) (Nat.add (nat_lit
      1) (Nat.shiftLeft CFSG.KD.ThB.ND (nat_lit 20))) (Nat.beq i (nat_lit 94)))

end CFSG.KD.ThB.C_4

#kc_each_unfold CFSG.KD.ThB.C_4.ok 80 95 as CFSG.KD.ThB.c
  eval CFSG.KD.ThB.C_4.lo CFSG.KD.ThB.C_4.acc

end
