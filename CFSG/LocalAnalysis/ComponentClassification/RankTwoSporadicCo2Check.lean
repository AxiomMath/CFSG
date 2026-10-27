module

public import Certificates.Certificate15009

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co2

open CFSG.Sporadic.Co2Cert

theorem co2_check :
    YCensus17 (co2P.subgroupOf co2P) (fun _ => False) := by
  obtain ⟨_, _, _, h⟩ := Certificates.certificate15009
  exact co2_yCensus17R h

theorem sporadicCaseOdd_Co2
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Co2 :=
  sporadicCaseOdd_Co2_of_check co2_check h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.Co2
