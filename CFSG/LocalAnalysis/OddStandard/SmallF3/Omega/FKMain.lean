module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKStd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAut
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (quadPlus nondegenerate_quadPlus)

section Main


theorem asc82OmegaPlusAutInvolutions_of_multNegOne (h : FKMultNegOne) :
    Asc82OmegaPlusAutInvolutions := by
  intro V _ _ _ Q hQ hdim hsign
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ (nondegenerate_quadPlus 4 (ZMod 3))
    (hdim.trans (by rw [Module.finrank_fintype_fun_eq_card]; decide))
    (hsign.trans (quadSign_quadPlus 4).symm)
  exact fkStmt_of_isometry hQ (nondegenerate_quadPlus 4 (ZMod 3)) e (by omega)
    (fkStmt_std_of_multNegOne h)

end Main

end CFSG.OddStandard.SmallF3.Omega
