module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcLieHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcSecRankFive
public import CFSG.LieType.Chevalley.E8WeylSectionalTwoRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

section Holds


theorem s2019FactExceptionalLie_of_secRank (hsec : S2019ExcSecRank) : S2019FactExceptionalLie :=
  s2019FactExceptionalLie_holds hsec s2019ExcCompNotRee_holds

end Holds

section Closed


theorem s2019FactExceptionalLie_holds' : S2019FactExceptionalLie :=
  s2019FactExceptionalLie_of_secRank
    (s2019ExcSecRank_of_weylGroup_E8 CFSG.LieType.Chevalley.sectionalTwoRankLE_weylGroup_E8)

end Closed

end CFSG.LocalAnalysis.GLTheoremA.S2019
