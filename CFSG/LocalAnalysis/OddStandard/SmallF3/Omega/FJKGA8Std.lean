module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8Std
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA8M
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8Surj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

theorem fjKGAAt_of_lieModel_minus_std {Y : Type} [Group Y] (h : LieModel Y .POmegaMinus 4 3 1)
    (h53 : ∀ (s : OGroup fa8Q0) (hs : s * s = 1), Fj53 fa8_std_nondegenerate hs) : FJKGAAt Y :=
  fjKGAAt_of_lieModel_minus h fa8_std_nondegenerate fa8_std_finrank fa8_std_quadSign
    (fa8_ffSimOmegaAct_surjective_std _ _) h53


theorem asc82CoreKGAHard_of_fj53 (hS : Asc82SchurU43) (hD4 : Asc82CoreKGAHardD4)
    (h53 : ∀ (s : OGroup fa8Q0) (hs : s * s = 1), Fj53 fa8_std_nondegenerate hs) :
    Asc82CoreKGAHard :=
  asc82CoreKGAHard_of_d4 hS hD4 fun (Y : Type) [Group Y] h =>
    fjKGAAt_of_lieModel_minus_std h h53

end CFSG.OddStandard.SmallF3.Omega
