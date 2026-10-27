module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Main8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3FinK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Cert
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Loc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Main7

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Blueprint.NativeSporadic

theorem fin76bInnerRest₈_holds :
    Fin76bInnerRest₈ :=
  fin76bInnerRest₈_of_rest₉ fin76bUCent
    (fin76bInnerRest₉_of_rest₁₀ fin76bEFacts69 fin76bFusion69
      (fin76bInnerRest₁₀_of_rest₁₁ fin76bEFacts69 fin76bFusion69
        (fin76bInnerRest₁₁_of_rest₁₃ fin76bEFacts69 fin76bFusion69 fin76bEFacts611
          fin76bInnerRest₁₃_holds)))

theorem j2_not_standard_of_outerParts {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hSolM : SolomonM10) (hLoc : Fin76bOuterS16Loc) (hPar : ExtremalParity)
    (h4 : Fin76bOuterS8₄) (h : StdHyp G L) : ¬ IsSporadic L .J2 :=
  j2_not_standard_of_rest₇ hSol
    (fin76bOuterRest₇_of_rest₈_models hSolM
      (fin76bOuterRest₈_of_rest₉
        (fin76bOuterRest₉_of_rest₁₀_cert
          (fin76bOuterRest₁₀_of_S (fin76bOuterS16_of_cent (fin76bOuterS16Cent_of_loc hPar hLoc))
            (fin76bOuterS8_of_s8₄_cert h4)))
        J2.outerEData_P J3.outerEData_j3P J2.outerInvData_Models_P J3.outerInvData_j3P))
    fin76bInnerRest₈_holds h

theorem j3_not_standard_of_outerParts {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hSol : SolomonZ2A6) (hSolM : SolomonM10) (hLoc : Fin76bOuterS16Loc) (hPar : ExtremalParity)
    (h4 : Fin76bOuterS8₄) (h : StdHyp G L) : ¬ IsSporadic L .J3 :=
  j3_not_standard_of_rest₇ hSol
    (fin76bOuterRest₇_of_rest₈_models hSolM
      (fin76bOuterRest₈_of_rest₉
        (fin76bOuterRest₉_of_rest₁₀_cert
          (fin76bOuterRest₁₀_of_S (fin76bOuterS16_of_cent (fin76bOuterS16Cent_of_loc hPar hLoc))
            (fin76bOuterS8_of_s8₄_cert h4)))
        J2.outerEData_P J3.outerEData_j3P J2.outerInvData_Models_P J3.outerInvData_j3P))
    fin76bInnerRest₈_holds h

end CFSG.EvenSporadicStandard.Fin76b
