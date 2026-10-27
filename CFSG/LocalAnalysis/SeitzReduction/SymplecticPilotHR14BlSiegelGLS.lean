module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegelRows
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


theorem spOmegaSiegelCentralInput_omegaPlus_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SpOmegaSiegelCentralInput .omegaPlus :=
  spOmegaSiegelCentralInput_omegaPlus_of_clauses
    (fun _ hm => LinearPilot.slmCatalogueClausesAt_of_inputs (by omega)
      (LinearPilot.slmEvenTypeDetAt (by omega)) hGLS (CrossChar.sLmNotOddLieInputAt (by omega))
      (LinearPilot.catSLmSporadicAt_of_four_le hm))
    (fun _ hm => LinearPilot.slmEvenTypeDetAt (by omega))

theorem spOmegaSiegelCentralInput_omegaMinus_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SpOmegaSiegelCentralInput .omegaMinus :=
  spOmegaSiegelCentralInput_omegaMinus_of_clauses
    (fun _ hm => LinearPilot.slmCatalogueClausesAt_of_inputs (by omega)
      (LinearPilot.slmEvenTypeDetAt (by omega)) hGLS (CrossChar.sLmNotOddLieInputAt (by omega))
      (LinearPilot.catSLmSporadicAt_of_four_le hm))
    (fun _ hm => LinearPilot.slmEvenTypeDetAt (by omega))

theorem spOmegaRowUniqueInput_omegaMinus_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SpOmegaRowUniqueInput .omegaMinus :=
  spOmegaRowUniqueInput_omegaMinus_of_central (spOmegaSiegelCentralInput_omegaMinus_of_gls3 hGLS)

theorem spOmegaRowUniqueInput_omegaPlus_of_gls3 (hGLS : GLS3OddLieAutComponentsInput)
    (hdata : OmegaMinusNonembeddingDataInput) (hmodel : OmegaLagrangianATwoModelInput) :
    SpOmegaRowUniqueInput .omegaPlus :=
  spOmegaRowUniqueInput_omegaPlus_of_central hdata hmodel
    (spOmegaSiegelCentralInput_omegaPlus_of_gls3 hGLS)

end CFSG.SeitzReduction.SymplecticPilot
