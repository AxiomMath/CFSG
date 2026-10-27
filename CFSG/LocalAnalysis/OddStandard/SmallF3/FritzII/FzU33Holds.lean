module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtLab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtGZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtGT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCtxHolds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbGH74Holds
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCFinal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB4D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Excl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10NoA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP11g

public section

namespace CFSG.OddStandard.SmallF3.FritzII

theorem smallF3U33Core_of_fz59
    (h59 : Fz59) : SmallF3U33Core :=
  smallF3U33Core_of_fritz CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models
      CFSG.Milestones.cl_lit_classical_involution_theorem_models
      (HarrisU33.harris1981_bound_of_gh74ModelsInput
          CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models) (fritzFusionInput_of_labels
              fzInvolT_holds fzInvolZ_holds fzSylR3_holds fzJFailsR3_holds fzCalZPairR3_holds
              fzJtWitness_holds)
      fritzCtxInput_holds fzc_caseI (fzb_of_struct fzbs_struct)
      (fzY7_of_split fzl_316 (fz37R_of_35b fzl_35b) fzl_410) (fzY8_of_split fzl_316 fzl_319 h59)
      (fzr_y10_of_split fzr_excl fzr_types fzr_noA fzr_noB fzr_shape) (fzSylowOfClosure_of_hall CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian)

end CFSG.OddStandard.SmallF3.FritzII
