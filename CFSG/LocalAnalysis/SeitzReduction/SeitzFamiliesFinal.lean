module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesXChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

section Large

theorem seitzExclusion_highE8_of_final (hGLS : GLS3OddLieAutComponentsInput)
    (h2 : E8Pilot.E8TwoInput) : SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_xchar hGLS monsterInnerInput monsterLocalComponentsInput h2

end Large

end CFSG.SeitzReduction
