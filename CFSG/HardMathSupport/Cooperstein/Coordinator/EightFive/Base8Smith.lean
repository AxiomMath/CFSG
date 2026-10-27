module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Defs
public import CFSG.Quasithin.Background.SmithB42LnL42

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

theorem b42L42Core_holds : B42L42Core :=
  fun _ _ _ hV _ _ hHyp hL _ hA => asB42L42_holds_core hV hHyp hL hA

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
