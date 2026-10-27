module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBThmB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1Lem11
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1Lem12

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Outside_of (h36 : Asc82Lemma36) : Asc82Outside where
  thm2L := asc82Thm2LConj_of_lemma36 h36
  lemma11 := asc82Lemma11_holds
  lemma12 := asc82Lemma12_holds

end CFSG.OddStandard.SmallF3.Omega
