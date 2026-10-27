module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.CJSuz2B.JF "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/JF.bin" 6 18205871448537299735
#kc_repo #kc_items_root CFSG.KD.CJSuz2B.loF "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/facts_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.CJSuz2B.accF "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/facts_acc.bin" 18 14981094727528566642
#kc_repo #kc_items_root CFSG.KD.CJSuz2B.JV "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/JV.bin" 11 10004994690038286758
#kc_repo #kc_items_root CFSG.KD.CJSuz2B.loC "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/cover_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.CJSuz2B.accC "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/tab/cover_acc.bin" 10 15916976828904412554

namespace CFSG.KD.CJSuz2B

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 2)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 1) (nat_lit 2)) JV loC accC i

end CFSG.KD.CJSuz2B

end
