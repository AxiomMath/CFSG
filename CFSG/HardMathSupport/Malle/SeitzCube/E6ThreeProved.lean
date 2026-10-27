module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4LinesFinal

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube


theorem excCubeHighAt_E6_three_proved : ExcCubeHighAt TauCeti.LieTypeIndex.E6 3 :=
  excCubeHighAt_E6_three_of_d4Lines
    (e6ThreeD4Lines_proved CFSG.Goldschmidt.topStatement)

end CFSG.HardMathSupport.Malle.SeitzCube
