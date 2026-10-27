module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralInst
public import CFSG.LocalAnalysis.OddStandard.Harada75

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG CFSG.ComponentClassification.HarrisLit

theorem harrisSolomonDihedralInput :
    HarrisSolomonDihedralInput := by
  intro X _ _ _ _ hX t L p f h
  exact dihedralStructure_of_core h fun S hS =>
    coreAt_of_config CFSG.OddStandard.Harada75.haradaInput_holds hX h hS

end CFSG.ComponentClassification.HSDihedral
