module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesXCharCat

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section XChar

theorem spFourOrthInput_of_xchar (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : LinearPilot.CatSLmSporadicAt 4) : SpFourOrthInput :=
  spFourOrthInput_of_catalogue
    (slmCatalogueClausesAt_of_xchar (by norm_num) (LinearPilot.slmEvenTypeDetAt (by norm_num))
      hGLS hSpor)

end XChar

end CFSG.SeitzReduction.SymplecticPilot
