module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadAll
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspPsuGood
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadAll
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHAll
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutG2
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeG2
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4
public import CFSG.HardMathSupport.Dickson.KD.CharP

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923

section


theorem i1431LieRest_of_remaining (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h0 : L2CentreThree) (hKD : KDCharP 3) (hB : CFSG.TauCetiBridge.TypewiseBridges)
    (hGA : GriessAllModelsStatement) (hD4 : Y1431_D4) (hU6 : Y1431LieRestAt
        FamU6Real) (hF4 : ExcResidual FamF4)
    (hE6Good : ExcResidual FamE6Good) (hE6Bad : Y1431_E6Bad) (hTwE6Good : ExcResidual FamTwE6Good)
    (hTwE6Bad : Y1431_TwE6Bad) (hE7 : ExcResidual FamE7) (hE8 : ExcResidual FamE8) :
    I1431LieRest :=
  i1431LieRest_of_families hO h0 (y1431_noCfg_pslGood h0 hO hKD) (y1431_noCfg_pslBad hO hGA)
    (y1431_noCfg_psp h0 hO hKD)
    (y1431_pspTwoEight_of_low h0 outDerived3_pspLow noE27_pspLow)
    (y1431_noCfg_psuGood h0 hO hKD) (y1431_noCfg_psuBad hO hGA) hU6
    (y1431_noCfg_orthOdd hO hKD) (y1431_noCfg_orthPlus hO hKD) (y1431_noCfg_orthMinus hO hKD) hD4
    (y1431_triD4_of_low h0 outDerived3_triD4Low noE27_triD4Low
      (y1431_noCfg_triD4High hKD hB outDerived3_triD4High))
    (y1431_g2_of_low h0 outDerived3_g2Low noE27_g2Low (y1431_noCfg_g2High hKD hB (noL2OuterAt_g2 hO)))
    (y1431_noCfg_of_excResidual hF4) (y1431_noCfg_of_excResidual hE6Good) hE6Bad
    (y1431_noCfg_of_excResidual hTwE6Good) hTwE6Bad (y1431_noCfg_of_excResidual hE7)
    (y1431_noCfg_of_excResidual hE8) (y1431_noCfg_reeG2 hKD hB (noL2OuterAt_reeg2 hO))
    (y1431_reeF4_of_rank h0 outDerived3_reeF4 noE27_reeF4)

end

section Open


theorem i1431LieRest_of_open (hR : D4RootSL2) (hU6 : Y1431LieRestAt FamU6Real) (hE6B : Y1431_E6Bad)
    (hTwE6B : Y1431_TwE6Bad) (hF4 : ExcResidual FamF4) (hE6G : ExcResidual FamE6Good)
    (hTwE6G : ExcResidual FamTwE6Good) (hE7 : ExcResidual FamE7) (hE8 : ExcResidual FamE8) :
    I1431LieRest :=
  i1431LieRest_of_remaining CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Solomon.Coordinator.l2CentreThree_holds
    (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds Nat.prime_three (by norm_num))
    CFSG.TauCetiBridge.typewiseBridges
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (y1431_D4_of_rootSL2 hR) hU6 hF4 hE6G hE6B hTwE6G hTwE6B hE7 hE8

end Open

end CFSG.HardMathSupport.Dickson.Sec6.I1431
