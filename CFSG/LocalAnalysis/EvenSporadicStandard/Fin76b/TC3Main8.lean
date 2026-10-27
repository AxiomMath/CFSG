module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HJ2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HJ3Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2HJ3Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2J2Data

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2PermEquiv j3PermEquiv)

theorem J2.betaDataSqBO_Models_P :
    BetaDataSqBO ↥ComponentClassification.J2Cover.Models.P :=
  BetaDataSqBO.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    J2.betaDataSqBO_j2P

theorem J2.outerInvData_Models_P :
    OuterInvData ↥ComponentClassification.J2Cover.Models.P :=
  OuterInvData.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    J2.outerInvData_j2P

theorem fin76bOuterRest₇_of_rest₈_models
    (hSol : SolomonM10) (hR : Fin76bOuterRest₈) : Fin76bOuterRest₇ :=
  fin76bOuterRest₇_of_rest₈ hSol hR J2.outerEData_P J3.outerEData_j3P J2.betaDataSqBO_Models_P
    J3.betaDataSqBO_j3P

end CFSG.EvenSporadicStandard.Fin76b
