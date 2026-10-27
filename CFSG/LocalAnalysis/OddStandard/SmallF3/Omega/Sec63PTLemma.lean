module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PArrow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma63_of_fbar (h33 : Asc82Lemma33) (h35 : Asc82Lemma35) (h36 : Asc82Lemma36)
    (hsh : Asc82Shapes) (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hF : Asc82AutFacts)
    (hbar : Asc82FactOm6PA6Bar) : Asc82Lemma63 :=
  asc82Lemma63_of' h33 h35 h36 hsh hP hM hF (asc82FactOm6PA6_of_fbar hbar)

end CFSG.OddStandard.SmallF3.Omega
