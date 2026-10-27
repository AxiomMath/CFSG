module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Moved

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family

theorem j4ExclusionProp_of_outerOdd
    (ha : J4OuterOddProp) : J4ExclusionProp :=
  j4ExclusionProp_of ha j4TwoRank j4MovedRank

theorem sporadicExclusion_J4_of_outerOdd
    (ha : J4OuterOddProp) : SporadicExclusion .J4 :=
  sporadicExclusion_J4_of ha j4TwoRank j4MovedRank

end CFSG.QuasithinUnique.Setup.X1
