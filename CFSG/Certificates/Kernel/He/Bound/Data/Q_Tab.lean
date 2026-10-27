module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.He.Bound.Data.Q_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.HeBQ.loF "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/facts_lo.bin" 230 10363588420620468723
#kc_repo #kc_items_root CFSG.KD.HeBQ.accF "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/facts_acc.bin" 389 1271762970889495078
#kc_repo #kc_items_root CFSG.KD.HeBQ.JF "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/JF.bin" 1089145 16063141271091057176
#kc_repo #kc_items_root CFSG.KD.HeBQ.loC "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/cover_lo.bin" 27 2727241441830674915
#kc_repo #kc_items_root CFSG.KD.HeBQ.accC "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/cover_acc.bin" 29 858061198448226023
#kc_repo #kc_items_root CFSG.KD.HeBQ.JV "CFSG/Certificates/Kernel/He/Bound/Checks/data/Q/tab/JV.bin" 23667 5258655728908647920

namespace CFSG.KD.HeBQ

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 46669) (nat_lit 4)) JV loC accC i

end CFSG.KD.HeBQ

end
