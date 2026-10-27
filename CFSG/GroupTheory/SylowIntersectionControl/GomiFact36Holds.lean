module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36IdentHolds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4Odd
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefReduction
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Faithful
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Homog
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36NatStab
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Overgroups

public section

namespace CFSG.GroupTheory

theorem gomiFact36ChiefFactors_holds :
    GomiFact36ChiefFactors :=
  gomiFact36ChiefFactors_of_inputs gomiFact36Identification_holds gomiFact36Homogeneity_holds
    (gomiFact36Faithful_of gomiFact36Identification_holds
      CFSG.QuasithinUnique.Lin2.sp4OddMultiplierTrivial)

theorem gomiFact36_holds :
    GomiFact36 :=
  gomiFact36_of_inputs gomiFact36ChiefFactors_holds gomiFact36NatStab_holds
    gomiFact36Overgroups_holds

end CFSG.GroupTheory

end
