module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34G2Q8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G2

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma34b_of_remaining_inputs (hS : Asc82SchurU43) : Asc82Lemma34b :=
  asc82Lemma34b_of_inputs_q8 asc82NoQ8InL2_holds asc82OddCoreCentralizerQ8_holds
    (asc82Q8Pocket_of_inputs asc82PocketCover_holds asc82Omega8PlusPocket_holds hS)

theorem asc82Lemma34_of_remaining_inputs (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hS : Asc82SchurU43) :
    Asc82Lemma34a ∧ Asc82Lemma34b ∧ Asc82Lemma34c :=
  ⟨asc82Lemma34a_of_inputs hT2 hC1, asc82Lemma34b_of_remaining_inputs hS,
    asc82Lemma34c_of_inputs_q8 hT2 hC1 hC3 asc82NoQ8InL2_holds asc82OddCoreCentralizerQ8_holds
      hS⟩

end CFSG.OddStandard.SmallF3.Omega
