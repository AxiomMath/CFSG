module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpC
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFinal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSuz
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.ComponentClassification.Sol76.Sig

theorem forcedSharedRankTwoFor_holds :
    ForcedSharedRankTwoFor :=
  forcedSharedRankTwoFor_of_symplectic (Sol76T13.R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz
      Sol76T13.R12.Pcls.sporadicCoverRankInput_Suz)
    TBLit.griessMultipliersAllModels_holds

end CFSG.ComponentClassification.Sol76.Sig
