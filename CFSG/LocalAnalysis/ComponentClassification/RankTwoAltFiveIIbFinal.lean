module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbStep5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIaJ2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveReduce
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem asc310IIb
    :
    Asc310IIb :=
  asc310IIb_of_steps asc310IIbStep4 asc310IIbStep56

theorem asc08Lemma310
    :
    RankTwoClassical.Asc08Lemma310 :=
  asc08Lemma310_of_local
    (asc08Lemma310Local_of_cases (asc310IIa_of' (asc310EpsOne_of Asc76X.goldschmidtTheoremA))
      asc310IIb)
    RankTwoFoundation.lemma32 RankTwoFoundation.lemma33Two RankTwoFoundation.section3Config

end CFSG.ComponentClassification.RankTwoAltFive
