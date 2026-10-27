module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2J2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2HJ3Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Rest7

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2PermEquiv j3PermEquiv)

theorem J2.betaDataSqB_Models_P :
    BetaDataSqB ↥ComponentClassification.J2Cover.Models.P :=
  BetaDataSqB.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    J2.betaDataSqB_j2P

theorem fin76bOuterRest_of_rest₇_models
    (hR : Fin76bOuterRest₇) : Fin76bOuterRest :=
  fin76bOuterRest_of_rest₇ hR J2.outerEData_P J3.outerEData_j3P J2.rootFactsClass_P
    J3.rootFactsClass_j3P J2.betaDataSqB_Models_P J3.betaDataSqB_j3P

theorem fin76bThmCSimple_of_rest₇_models
    (hR : Fin76bOuterRest₇) : Fin76bThmCSimple :=
  fin76bThmCSimple_of_outerRest_models (fin76bOuterRest_of_rest₇_models hR)

theorem j2_not_standard_of_rest₇ {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hO : Fin76bOuterRest₇) (hR : Fin76bInnerRest₈) (h : StdHyp G L) :
    ¬ IsSporadic L .J2 :=
  j2_not_standard_of_rest₈_simple hSol (fin76bThmCSimple_of_rest₇_models hO) hR h

theorem j3_not_standard_of_rest₇ {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hO : Fin76bOuterRest₇) (hR : Fin76bInnerRest₈) (h : StdHyp G L) :
    ¬ IsSporadic L .J3 :=
  j3_not_standard_of_rest₈_simple hSol (fin76bThmCSimple_of_rest₇_models hO) hR h

end CFSG.EvenSporadicStandard.Fin76b
