module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Exceptional
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Bender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.ExcUntwisted
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.E6Twisted
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthCharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthPlus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.OrthMinus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSUTorus

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem asLieTwo_of_open
    (hPSU : AsLieTwoPSUGe4)
    (hOp : AsLieTwoAt .POmegaPlus) (hOm : AsLieTwoAt .POmegaMinus) :
    AsLieTwoOvergroups ∧ AsLieTwoSylowAut := by
  refine asLieTwo_of_tags (fun t => ?_) asLieTwoPSU33_holds
  cases t
  · exact asLieTwoAt_psl_of asLieTwoPSLGe4_holds
  · exact asLieTwoAt_psu_of hPSU
  · exact asLieTwoAt_psp_of asLieTwoPSpGe3_holds
  · exact asLieTwoAt_pOmegaOdd
  · exact hOp
  · exact hOm
  · exact asLieTwoAt_g2
  · exact asLieTwoAt_f4
  · exact asLieTwoAt_e6
  · exact asLieTwoAt_e7
  · exact asLieTwoAt_e8
  · exact asLieTwoAt_twistedE6
  · exact asLieTwoAt_trialityD4
  · exact asLieTwoAt_twistedB2
  · exact asLieTwoAt_twistedG2
  · exact asLieTwoAt_twistedF4
  · exact asLieTwoAt_tits

theorem asLieTwo_of_gaps
    (hT : PSUTorusOvergroup) :
    AsLieTwoOvergroups ∧ AsLieTwoSylowAut :=
  asLieTwo_of_open (asLieTwoPSUGe4_of_gaps (psuCover_of_torus hT) (psu42SylowFacts_of_torus hT))
    (asLieTwoAt_pOmegaPlus_of_gaps pOmegaPlusCover_holds pOmegaPlusCharTwo_holds
      pOmegaPlusCoatom_holds)
    (asLieTwoAt_pOmegaMinus_of_gaps pOmegaMinusCover_holds pOmegaMinusCharTwo_holds
      pOmegaMinusCoatom_holds)

theorem asLieTwo_holds :
    AsLieTwoOvergroups ∧ AsLieTwoSylowAut :=
  asLieTwo_of_gaps psuTorusOvergroup_holds

end CFSG.Quasithin.LieOver
