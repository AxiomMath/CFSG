module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Assembly
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactCentralOmega_of_tables (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    KFactCentralOmega :=
  CentralOmega.kFactCentralOmega_of_reduced
    (CentralOmega.centralOmegaReduced_of_tables hGA hAlt hSpor)

section Holds


theorem kFactCentralOmega_holds : KFactCentralOmega :=
  kFactCentralOmega_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC
