module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.McL.Data.CQ
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.McL.CQ.loF "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/facts_lo.bin" 5240 11127648619597029260
#kc_repo #kc_items_root CFSG.KD.McL.CQ.accF "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/facts_acc.bin" 9562 2107599457879900149
#kc_repo #kc_items_root CFSG.KD.McL.CQ.JF "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/JF.bin" 23925802 3517372542009794354
#kc_repo #kc_items_root CFSG.KD.McL.CQ.loC "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/cover_lo.bin" 611 1941610378224692050
#kc_repo #kc_items_root CFSG.KD.McL.CQ.accC "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/cover_acc.bin" 694 18115585787421242987
#kc_repo #kc_items_root CFSG.KD.McL.CQ.JV "CFSG/Certificates/Kernel/McL/Checks/data/CQ/tab/JV.bin" 875147 1932181821665622504

namespace CFSG.KD.McL.CQ

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 6)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs nF (nat_lit 6)) JV loC accC i

end CFSG.KD.McL.CQ

end
