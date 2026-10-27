module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Uniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Final
public import Certificates.Certificate27260

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 (SylowFacts sylowFacts_of_checks)

theorem sylowFacts_of_cert : SylowFacts := by
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate27260
  exact sylowFacts_of_checks h1 h2 h3 h4

theorem sol78Lemma65Uniq_of_certs :
    Sol78Lemma65Uniq :=
  sol78Lemma65Uniq_of_facts m23Facts_of_certs sylowFacts_of_cert

end CFSG.EvenSporadicStandard.Induction.Balance
