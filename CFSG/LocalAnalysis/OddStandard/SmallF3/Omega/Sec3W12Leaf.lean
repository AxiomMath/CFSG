module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma311_of_remaining_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) (hstd : Asc82StandardInputF)
    (hOuter : Asc82OmegaPlusOuter) (hCl : Asc82OmegaPlusClosure) (hGen : Asc82OmegaPlusGen) :
    Asc82Lemma311 :=
  asc82Lemma311_of_standardInputF hT2 hC1 hC3 hS hstd asc82OmegaPlusProjInner_holds hOuter hCl
    hGen

theorem aschOmega8Plus_of_remaining_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) (hstd : Asc82StandardInputF)
    (hOuter : Asc82OmegaPlusOuter) (hCl : Asc82OmegaPlusClosure) (hGen : Asc82OmegaPlusGen) :
    AschOmega8Plus :=
  asc82Lemma311_of_remaining_inputs hT2 hC1 hC3 hS hstd hOuter hCl hGen

end CFSG.OddStandard.SmallF3.Omega
