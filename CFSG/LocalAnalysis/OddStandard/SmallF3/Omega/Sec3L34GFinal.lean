module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GM3

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma34_of_finite_facts (hT2 : Asc82Thm2Q) (hS : Asc82SchurU43) (hCor : Asc82CorIII)
    (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3) (hM3 : Asc82SchurOdd3)
    (hNF : Asc82FactNoncentralFixed) (hKA : Asc82FactPocketComp) (hKB : Asc82FactPocketLift) :
    Asc82Lemma34a ∧ Asc82Lemma34b ∧ Asc82Lemma34c :=
  asc82Lemma34_of_facts hT2 (asc82CommuteStep_of_facts hO3 hC3 hM3 hNF) hS hCor hNF hKA hKB

theorem asc82Lemma34_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) (hT2 : Asc82Thm2Q)
    (hS : Asc82SchurU43) (hCor : Asc82CorIII) (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3)
    (hNF : Asc82FactNoncentralFixed) (hKA : Asc82FactPocketComp) (hKB : Asc82FactPocketLift) :
    Asc82Lemma34a ∧ Asc82Lemma34b ∧ Asc82Lemma34c :=
  asc82Lemma34_of_finite_facts hT2 hS hCor hO3 hC3 (l34g_schurOdd3_of_griess hGA) hNF hKA hKB

end CFSG.OddStandard.SmallF3.Omega
