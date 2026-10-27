module

public import CFSG.HardMathSupport.Lang.SeitzPlane.Vacuous
public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE6
public import CFSG.HardMathSupport.Malle.Proving.ExcPlaneRest
public import CFSG.LieType.SeitzGeneration.ExcPlaneAssembly

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Malle.Proving
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator


theorem excPlaneE8_proved : ExcPlaneE8 :=
  excPlaneE8_of_parts excPlaneE8Low excPlaneE8E3_proved excPlaneE8E4_proved excPlaneE8E6_proved
    excPlaneE8Rest_proved

theorem excPlaneE6_proved : ExcPlaneE6 :=
  excPlaneE6_of_parts excPlaneE6Low excPlaneE6E3_proved excPlaneE6Rest_proved

theorem excPlaneE7_of_E6 (h : ExcPlaneE7E6) : ExcPlaneE7 :=
  excPlaneE7_of_parts excPlaneE7Low excPlaneE7E3_proved h excPlaneE7Rest_proved

theorem excParabolicPlane_of_open
    (htw : ExcPlaneTwistedE6)
    (h76 : ExcPlaneE7E6) :
    ExcParabolicPlane :=
  excParabolicPlane_of_residuals
    { g2Three := excPlaneG2Three
      trialityOddFive := CFSG.HardMathSupport.Lang.SeitzPlane.excPlaneTrialityOddFive
      trialityThree := CFSG.HardMathSupport.Lang.SeitzPlane.excPlaneTrialityThree
      reeF4Three := CFSG.HardMathSupport.Lang.SeitzPlane.excPlaneReeF4Three
      f4 := excPlaneF4
      e6 := excPlaneE6_proved
      twistedE6 := htw
      e7 := excPlaneE7_of_E6 h76
      e8 := excPlaneE8_proved }

end CFSG.HardMathSupport.Malle.SeitzCube
