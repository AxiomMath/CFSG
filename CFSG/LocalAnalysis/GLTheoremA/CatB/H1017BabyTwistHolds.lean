module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPure
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureA
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureBHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureC
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS


theorem i1017BabyTwist_holds
    : I1017BabyTwist :=
  i1017BabyTwist_of_threeB (babyTwistThreeB_of_noPureFour fun k => by
    fin_cases k
    · exact babyNoPureFourAt_zero
    · exact babyNoPureFourAt_one_holds
    · exact babyNoPureFourAt_two
    · exact babyNoPureFourAt_three_of_zero babyNoPureFourAt_zero)

end CFSG.LocalAnalysis.GLTheoremA.H1017
