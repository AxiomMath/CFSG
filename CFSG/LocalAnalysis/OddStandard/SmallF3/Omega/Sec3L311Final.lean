module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Disch
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L36
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L37
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkExists
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma38_of_named_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) : Asc82Lemma38 := by
  have h34 := asc82Lemma34_of_remaining_inputs hT2 hC1 hC3 hS
  have h35 := asc82Lemma35_of_34c h34.2.2
  have h36 := asc82Lemma36_of_35 h35 (asc82PocketExists_of_schur hS)
  exact asc82Lemma38_of_37F (asc82Lemma37F_of_35_36 h35 h36) asc82Omega8MinusData_holds

theorem aschOmega8Minus_of_named_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) : AschOmega8Minus :=
  asc82Lemma38_of_named_inputs hT2 hC1 hC3 hS

end CFSG.OddStandard.SmallF3.Omega
