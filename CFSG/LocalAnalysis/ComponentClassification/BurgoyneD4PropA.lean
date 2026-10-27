module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4T2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Conj

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG.ComponentClassification.TBLit

theorem burgoynePropA_of_E1_E2 (hE1 : BurgoyneExcOddCoreInput) (hE2 : BurgoynePropAE6E7) :
    BurgoynePropA :=
  burgoynePropA_of_T2_E1_E2 burgoyneD4TrialityOddCoreInput_holds hE1 hE2

end CFSG.ComponentClassification.Burgoyne
