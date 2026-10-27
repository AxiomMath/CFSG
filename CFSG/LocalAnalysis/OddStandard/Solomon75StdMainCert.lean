module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bCert

public section

namespace CFSG.OddStandard.Solomon75

theorem solomon2AnStdCyclic_of_core
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput) (hCore : Solomon2AnStdCore) :
    Solomon2AnStdCyclic :=
  solomon2AnStdCyclic_of_theorem44 solomon44McL_of_certificate
    (solomon44Ly_of_gh74_of_certificate hGH) solomon44NineTen_of_certificate hCore

end CFSG.OddStandard.Solomon75
