module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8High
public import CFSG.HardMathSupport.Malle.SeitzCube.E8ThreeCube
public import CFSG.HardMathSupport.Malle.SeitzCube.E8FourCube
public import CFSG.HardMathSupport.Malle.SeitzCube.E8SixCube

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.LieType.SeitzGeneration

section All


theorem excCubeHigh_E8 : ExcCubeHigh .E8 TauCeti.LieTypeIndex.E8 :=
  excCubeHigh_E8_of_twisted twistedCubeE8_three twistedCubeE8_four twistedCubeE8_six

end All

end CFSG.HardMathSupport.Malle.SeitzCube
