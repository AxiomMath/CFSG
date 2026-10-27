module

public import Certificates.Certificate15013

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

theorem fi23_fourCheck : fi23FourCheck fi23FourSlp fi23FourX fi23FourZ = true :=
  Certificates.certificate15013

theorem transpositionOrderFour :
    TranspositionOrderFour :=
  transpositionOrderFour_of_check fi23_fourCheck

theorem twoAOrderFour :
    TwoAOrderFour :=
  twoAOrderFour_of_check fi23_fourCheck

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
