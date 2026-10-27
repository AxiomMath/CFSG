module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.He.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.HeBP.loF "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/facts_lo.bin" 6788 16449082353814852177
#kc_repo #kc_items_root CFSG.KD.HeBP.accF "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/facts_acc.bin" 12417 11660557480041617827
#kc_repo #kc_items_root CFSG.KD.HeBP.JF "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/JF.bin" 33350571 6334749249800300101
#kc_repo #kc_items_root CFSG.KD.HeBP.loC "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/cover_lo.bin" 1627 4601405993828010910
#kc_repo #kc_items_root CFSG.KD.HeBP.accC "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/cover_acc.bin" 1872 4159247525779503960
#kc_repo #kc_items_root CFSG.KD.HeBP.JV "CFSG/Certificates/Kernel/He/Bound/Checks/data/P/tab/JV.bin" 8618794 16094871582073547769

namespace CFSG.KD.HeBP

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 1157714) (nat_lit 4)) JV loC accC i

end CFSG.KD.HeBP

end
