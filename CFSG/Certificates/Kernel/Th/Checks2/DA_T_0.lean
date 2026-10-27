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

#kc_repo #kc_items_root CFSG.KD.ThA.T_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_T_0_J.bin" 8778 10766403386279946552
#kc_repo #kc_items_root CFSG.KD.ThA.T_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_T_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThA.T_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_T_0_acc.bin" 5 16058875513670357405

namespace CFSG.KD.ThA.T_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runT CFSG.KD.ThA.HB CFSG.KD.ThA.TB CFSG.KD.ThA.OB CFSG.KD.ThA.RR
      CFSG.KD.ThA.FB CFSG.KD.ThA.LT CFSG.KD.ThA.TL CFSG.KD.ThA.VL CFSG.KD.ThA.NL CFSG.KD.ThA.NR
      CFSG.KD.ThA.nH CFSG.KD.ThA.nT CFSG.KD.ThA.osh CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB
      CFSG.KD.ThA.sel CFSG.KD.ThA.I0 (nat_lit 4) (nat_lit 2336) (nat_lit 0) (CFSG.KC.LceSeg.seg
      CFSG.KD.ThA.T_0.J (CFSG.KD.ThA.T_0.lo (i + 1) - CFSG.KD.ThA.T_0.lo i) (CFSG.KD.ThA.T_0.lo i))
      (CFSG.KD.ThA.T_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThA.T_0.acc (i + 1))
      (Nat.succ CFSG.KD.ThA.nT) (Nat.beq i (nat_lit 0)))

end CFSG.KD.ThA.T_0

#kc_each_unfold CFSG.KD.ThA.T_0.ok 0 1 as CFSG.KD.ThA.t
  eval CFSG.KD.ThA.T_0.lo CFSG.KD.ThA.T_0.acc

end
