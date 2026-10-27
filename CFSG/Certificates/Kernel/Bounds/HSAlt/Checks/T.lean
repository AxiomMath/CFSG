module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.T_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.HSKT.loF "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/facts_lo.bin" 140 7069849918947172729
#kc_repo #kc_items_root CFSG.KD.HSKT.accF "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/facts_acc.bin" 239 14823878400936143691
#kc_repo #kc_items_root CFSG.KD.HSKT.JF "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/JF.bin" 615244 15531413747541288494
#kc_repo #kc_items_root CFSG.KD.HSKT.loC "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/cover_lo.bin" 32 12702425685512842426
#kc_repo #kc_items_root CFSG.KD.HSKT.accC "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/cover_acc.bin" 35 11253682890150782190
#kc_repo #kc_items_root CFSG.KD.HSKT.JV "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/tab/JV.bin" 92092 11457084764560200943

namespace CFSG.KD.HSKT

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 42324) (nat_lit 4)) JV loC accC i

theorem okW_all : ∀ t < 23, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 5, okC t = true := by
  kc_cover 1

end CFSG.KD.HSKT

end
