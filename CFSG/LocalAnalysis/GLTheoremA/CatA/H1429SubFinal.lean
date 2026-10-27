module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA


theorem i1429SubSimple_holds : I1429SubSimple :=
  i1429SubSimple_of_families (kdAmbSolv_holds Nat.prime_three (by norm_num)
    u42_fixSubgroup_solvable) i1429SubLin_holds i1429SubUni_holds i1429SubSymp_holds
    i1429SubOrth_holds i1429SubD4_holds i1429SubExc_holds i1429SubTwE6_holds i1429SubTri_holds
    i1429SubRee_holds

theorem i1429SubfieldOut_holds : I1429SubfieldOut :=
  i1429SubfieldOut_of_simple i1429SubSimple_holds

end CFSG.LocalAnalysis.GLTheoremA

end
