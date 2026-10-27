module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310CStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Disch
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L36
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L39
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkExists

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma311_of_standardInputF (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) (hstd : Asc82StandardInputF)
    (hproj : Asc82OmegaPlusProjInner) (hOuter : Asc82OmegaPlusOuter)
    (hCl : Asc82OmegaPlusClosure) (hGen : Asc82OmegaPlusGen) : Asc82Lemma311 := by
  have hPE := asc82PocketExists_of_schur hS
  have h34 := asc82Lemma34_of_remaining_inputs hT2 hC1 hC3 hS
  have h36 := asc82Lemma36_of_35 (asc82Lemma35_of_34c h34.2.2) hPE
  exact asc82Lemma311_of_inputs (asc82Lemma33F_of_inputs h36 hPE h34.2.2 hstd) h34.1 h34.2.2
    h36 (asc82Lemma39_of_36 h36) (asc82OmegaPlusInner_of_projInner hproj) hOuter
    asc82OmegaPlusPocketedConj_holds asc82OmegaPlusPocketLift_holds hCl asc82OmegaPlusCStar hPE
    hGen

end CFSG.OddStandard.SmallF3.Omega
