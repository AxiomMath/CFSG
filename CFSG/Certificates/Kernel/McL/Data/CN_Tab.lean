module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.McL.Data.CN
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.McL.CN.loF "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/facts_lo.bin" 193 13141602784265619586
#kc_repo #kc_items_root CFSG.KD.McL.CN.accF "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/facts_acc.bin" 329 12459611684144798417
#kc_repo #kc_items_root CFSG.KD.McL.CN.JF "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/JF.bin" 920685 173520918775570361
#kc_repo #kc_items_root CFSG.KD.McL.CN.loC "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/cover_lo.bin" 77 7975606178858723509
#kc_repo #kc_items_root CFSG.KD.McL.CN.accC "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/cover_acc.bin" 83 14383414374240733916
#kc_repo #kc_items_root CFSG.KD.McL.CN.JV "CFSG/Certificates/Kernel/McL/Checks/data/CN/tab/JV.bin" 389318 11337187645790560237

namespace CFSG.KD.McL.CN

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 6)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs nF (nat_lit 6)) JV loC accC i

end CFSG.KD.McL.CN

end
