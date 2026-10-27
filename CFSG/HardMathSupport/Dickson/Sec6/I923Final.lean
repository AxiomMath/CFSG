module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Families
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E7
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E8
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeG2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeF4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthOdd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthPlus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGood
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBad
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBad
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Reduced
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms

theorem y923LieRest_of_six (hPslBad : Y923_PslBad) (hPsuBad : Y923_PsuBad) (hD4 : Y923_D4)
    (hTriD4 : Y923_TriD4) (hE6 : Y923_E6) (hTwE6 : Y923_TwE6) : Y923_LieRest :=
  y923LieRest_of_families hPslBad y923_psuGood_holds hPsuBad y923_orthOdd_holds
    y923_orthPlus_holds y923_orthMinus_holds hD4 hTriD4 y923_g2_holds y923_f4_holds hE6 hTwE6
    y923_e7_holds y923_e8_holds y923_reeg2_holds y923_reef4_holds

theorem y923LieRest_holds : Y923_LieRest :=
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  y923LieRest_of_six (y923_pslbad_holds hGA) (y923_psuBad_holds hGA)
    (y923_d4_of_A2 triD4A2NoL2_holds) (y923_triD4_of_A2 triD4A2NoL2_holds) y923_e6_holds
    y923_twE6_holds

end CFSG.HardMathSupport.Dickson.Sec6.I923
