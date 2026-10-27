module

public import CFSG.LieType.SeitzGeneration.ExcPlaneSzTits
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.LieType.SeitzGeneration.ExcPlaneReeF4
public import CFSG.LieType.SeitzGeneration.ExcPlaneTriality

public section

namespace CFSG.LieType.SeitzGeneration

theorem excParabolicPlaneFree : ExcParabolicPlaneFree where
  suzuki := excPlaneSuzuki
  reeG2 := excPlaneReeG2
  tits := excPlaneTits
  g2Five := excPlaneG2Five
  reeF4Five := excPlaneReeF4Five
  trialityEvenFive := excPlaneTrialityEvenFive

theorem excParabolicPlane_of_residuals (hR : ExcParabolicPlaneResiduals) : ExcParabolicPlane :=
  excParabolicPlane_of_parts excParabolicPlaneFree hR

end CFSG.LieType.SeitzGeneration
