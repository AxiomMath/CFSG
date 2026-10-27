module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.P4_Sel
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X2_Sel
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X3_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.Co2KP4.loF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/facts_lo.bin" 632 4839557729421983906
#kc_repo #kc_items_root CFSG.KD.Co2KP4.accF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/facts_acc.bin" 1059 17346429854682106020
#kc_repo #kc_items_root CFSG.KD.Co2KP4.JF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/JF.bin" 3011779 1308896451959817790
#kc_repo #kc_items_root CFSG.KD.Co2KP4.loC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/cover_lo.bin" 157 14696451490638181647
#kc_repo #kc_items_root CFSG.KD.Co2KP4.accC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/cover_acc.bin" 161 1464220517526672513
#kc_repo #kc_items_root CFSG.KD.Co2KP4.JV "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/P4/tab/JV.bin" 754793 4786963951003022403
#kc_repo #kc_items_root CFSG.KD.Co2KX2.loF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/facts_lo.bin" 241 8731825028245906908
#kc_repo #kc_items_root CFSG.KD.Co2KX2.accF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/facts_acc.bin" 409 12631200777573506152
#kc_repo #kc_items_root CFSG.KD.Co2KX2.JF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/JF.bin" 1101718 8606617482156835343
#kc_repo #kc_items_root CFSG.KD.Co2KX2.loC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/cover_lo.bin" 50 10894002107662235812
#kc_repo #kc_items_root CFSG.KD.Co2KX2.accC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/cover_acc.bin" 53 5957195493380109154
#kc_repo #kc_items_root CFSG.KD.Co2KX2.JV "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X2/tab/JV.bin" 172384 12562046784924416247
#kc_repo #kc_items_root CFSG.KD.Co2KX3.loF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/facts_lo.bin" 386 1172156228445160251
#kc_repo #kc_items_root CFSG.KD.Co2KX3.accF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/facts_acc.bin" 649 12385163974312136762
#kc_repo #kc_items_root CFSG.KD.Co2KX3.JF "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/JF.bin" 1748275 714474409293478503
#kc_repo #kc_items_root CFSG.KD.Co2KX3.loC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/cover_lo.bin" 45 10737657559263561263
#kc_repo #kc_items_root CFSG.KD.Co2KX3.accC "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/cover_acc.bin" 47 7399980729600418891
#kc_repo #kc_items_root CFSG.KD.Co2KX3.JV "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/X3/tab/JV.bin" 47475 4090167280541733257

namespace CFSG.KD

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def Co2KP4.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Co2KP4.blk Co2KP4.selWT Co2KP4.INV Co2KP4.nC (nat_lit 4)) Co2KP4.JF
    Co2KP4.loF Co2KP4.accF i

@[expose] noncomputable def Co2KP4.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Co2KP4.blk Co2KP4.LVs (nat_lit 138182) (nat_lit 4)) Co2KP4.JV Co2KP4.loC
    Co2KP4.accC i

@[expose] noncomputable def Co2KX2.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Co2KX2.blk Co2KX2.selWT Co2KX2.INV Co2KX2.nC (nat_lit 8)) Co2KX2.JF
    Co2KX2.loF Co2KX2.accF i

@[expose] noncomputable def Co2KX2.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Co2KX2.blk Co2KX2.LVs (nat_lit 81493) (nat_lit 8)) Co2KX2.JV Co2KX2.loC
    Co2KX2.accC i

@[expose] noncomputable def Co2KX3.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Co2KX3.blk Co2KX3.selWT Co2KX3.INV Co2KX3.nC (nat_lit 10)) Co2KX3.JF
    Co2KX3.loF Co2KX3.accF i

@[expose] noncomputable def Co2KX3.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Co2KX3.blk Co2KX3.LVs (nat_lit 139657) (nat_lit 10)) Co2KX3.JV Co2KX3.loC
    Co2KX3.accC i

theorem Co2KP4.okW_all : ∀ t < 105, Co2KP4.okW t = true := by
  kc_cover 1

theorem Co2KP4.okC_all : ∀ t < 26, Co2KP4.okC t = true := by
  kc_cover 1

theorem Co2KX2.okW_all : ∀ t < 40, Co2KX2.okW t = true := by
  kc_cover 1

theorem Co2KX2.okC_all : ∀ t < 8, Co2KX2.okC t = true := by
  kc_cover 1

theorem Co2KX3.okW_all : ∀ t < 64, Co2KX3.okW t = true := by
  kc_cover 1

theorem Co2KX3.okC_all : ∀ t < 7, Co2KX3.okC t = true := by
  kc_cover 1

end CFSG.KD

end
