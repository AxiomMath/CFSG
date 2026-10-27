module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdMainCert
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdNZMain
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Holds

theorem solomon2AnStdCyclic_holds (hGH : ComponentClassification.UFrontier.GH74ModelsInput) :
    Solomon75.Solomon2AnStdCyclic :=
  Solomon75.solomon2AnStdCyclic_of_core hGH Solomon75.solomon2AnStdCore

end Holds

end CFSG.OddStandard
