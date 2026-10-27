module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TwistFi22

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017


theorem i1017FiTwoThreeTwist_holds : I1017FiTwoThreeTwist :=
  Fi23Twist.i1017FiTwoThreeTwist_of_facts i1017FiTwoTwoTwist_holds Fi23Twist.factB_holds
    Fi23Twist.factC_holds

end CFSG.LocalAnalysis.GLTheoremA.H1017
