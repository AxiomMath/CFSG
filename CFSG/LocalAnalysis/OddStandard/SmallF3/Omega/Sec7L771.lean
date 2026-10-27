module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L71
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L73
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74I4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74BX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma77a_of (hsh : Asc82Shapes) (h33 : Asc82Lemma33) (h36 : Asc82Lemma36)
    (h37 : Asc82Lemma37) (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hO : Asc82Outside)
    (hF5 : Asc82Fink5) (hE1 : Asc82E8Cent) (hE2 : Asc82E8Stab) : Asc82Lemma77a := by
  have h71 := asc82Lemma71_of hsh
  have h72 := asc82Lemma72_of h33 h71
  have h73 := asc82Lemma73_of h36 h37 hP
  have hBX := sec74BX_of h36 h72 h73 hP hF hO
  have h74 := asc82Lemma74_of h36 h72 hP (sec74NotI4_of h36 h72 h73 hP hF)
    (sec74CaseC_of h36 h72 h73 hP hF hO)
    (sec74CaseB_of h36 h72 h73 hP hF hBX (sec74BT_of h36 h72 hP hBX))
  have h76 := asc82Lemma76_of h36 h72 h73 h74 hP hO hF5
  intro G _ _ t L S z g B hc
  exact sec7l771_main h36 h72 h73 h76 hP hF hE1 hE2 hc

end CFSG.OddStandard.SmallF3.Omega
