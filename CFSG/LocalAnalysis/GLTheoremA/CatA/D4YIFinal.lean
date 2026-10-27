module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YDNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YERest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YGRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIRest
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyInnerAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Cover
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.H13.J4Order
public import CFSG.RankThree.Native.ONTripleRed
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8140
public import Certificates.Certificate8141

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.LocalAnalysis.GLTheoremA.D4T

section Certs

set_option linter.unusedSectionVars false


theorem d4BigCoreAt_holds
    : D4BigCoreAt :=
  d4BigCoreAt_of_rest (d4BigCoreRest_of_rest2 d4BigCoreRest2_holds)

theorem noTrialityBigAt_holds
    {G : Type} [Group G] [Finite G] : NoTrialityBigAt G :=
  noTrialityBigAt_of_core d4BigCoreAt_holds (d4BigNormalizes_holds G)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Certs

end CFSG.LocalAnalysis.GLTheoremA.D4Y
