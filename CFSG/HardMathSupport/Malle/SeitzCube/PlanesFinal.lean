module

public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesAssembly
public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesE7E6
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Six
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Rest

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.SeitzPlane

theorem excParabolicPlane_proved :
    ExcParabolicPlane :=
  excParabolicPlane_of_open
    (excPlaneTwistedE6_of_parts excPlaneTwistedE6Low excPlaneTwistedE6Six excPlaneTwistedE6Rest)
    excPlaneE7E6_proved

end CFSG.HardMathSupport.Malle.SeitzCube
