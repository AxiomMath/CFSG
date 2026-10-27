module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4
public import CFSG.Sporadic.Recognition.J4Multiplier

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4

open CFSG.Sporadic.Recognition.J4Multiplier

theorem j4NoDoubleCover
    (hFox : J4FoxCert) (hForm : J4FormCert) :
    J4NoDoubleCover := by
  intro E _ π hπ hE
  exact noPerfectDoubleCover_J4 hFox hForm E π hπ hE

end CFSG.ComponentClassification.RankTwoSporadic.J4
