module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24OrdersCheck
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate2065
public import Certificates.Certificate2066
public import Certificates.Certificate2067
public import Certificates.Certificate2068
public import Certificates.Certificate2069
public import Certificates.Certificate2070
public import Certificates.Certificate2071
public import Certificates.Certificate2073
public import Certificates.Certificate2074
public import Certificates.Certificate2075
public import Certificates.Certificate2076
public import Certificates.Certificate2077
public import Certificates.Certificate2078
public import Certificates.Certificate3037
public import Certificates.Certificate3038
public import Certificates.Certificate3039
public import Certificates.Certificate3147
public import Certificates.Certificate3148
public import Certificates.Certificate3150
public import Certificates.Certificate3151
public import Certificates.Certificate3152
public import Certificates.Certificate3153
public import Certificates.Certificate3154
public import Certificates.Certificate3166
public import Certificates.Certificate6098
public import Certificates.Certificate15013
public import Certificates.Certificate15027
public import Certificates.Certificate15028

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

theorem sporadicCaseOdd_Fi24Prime
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .Fi24Prime := by
  obtain ⟨hP, hQ, hirr, hfaith, h4, hC⟩ := twoB_facts_checked
  exact sporadicCaseOdd_Fi24Prime_of_facts h32 h33 transpositionOrderFour twoAOrderFour
    twoACentralizer hP hQ hirr hfaith h4 hC

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
