module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentreAll
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

set_option linter.unusedSectionVars false


theorem kFactChevGenCentre_proved : CFSG.AGLEmbeddingD2.GN.KFactChevGenCentre :=
  kFactChevGenCentre_of_griess (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
