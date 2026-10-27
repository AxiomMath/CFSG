module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalHypII
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverO8Cert

public section

namespace CFSG.ComponentClassification.RankTwoClassical

theorem classicalHypIICover :
    ClassicalHypIICover := by
  intro A _ _ hA h
  rcases h with h | h | h
  · exact RankTwoHypIICover.U42.hypII_of_psu_four_two hA h
  · exact RankTwoHypIICover.U62.hypII_of_psu_six_two hA h
  · exact RankTwoHypIICover.O8.hypII_of_pomegaPlus_four_two hA h

theorem classicalHypII_of_multiplier
    (hM : ClassicalEvenMultiplier) : ClassicalHypII :=
  classicalHypII_of RankTwoHypIIOrthogonal.orthogonalHypIIOdd classicalHypIICover hM

end CFSG.ComponentClassification.RankTwoClassical
