module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

theorem u3ThreeNormalForm_holds :
    CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.U3ThreeNormalForm :=
  fun _ _ _ _ h hq2 hq3 _ _ hB hc => U3NF.u3Three_cube_normal_form h hq2 hq3 hB hc

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
