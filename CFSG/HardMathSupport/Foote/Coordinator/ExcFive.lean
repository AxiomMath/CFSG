module

public import CFSG.HardMathSupport.Foote.Coordinator.Shared
public import CFSG.HardMathSupport.Foote.ModuleExclusions.F4E6E8
public import CFSG.HardMathSupport.Foote.ModuleExclusions.E7
public import CFSG.HardMathSupport.Foote.ModuleExclusions.TwistedE6

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.Blueprint
open CFSG.RankThree.PartOne (ExceptionalCenterSmallPrimes)

theorem excFiveTarget_of_exceptionalCenterSmallPrimes
    (hECS : ExceptionalCenterSmallPrimes) : ExcFiveTarget := by
  intro Q _ t f ht hQ hpar
  cases t with
  | G2 => exact end415K_of_coverInv (ModuleExclusions.coverInv_g2_charFive hECS Q hQ)
  | F4 => exact end415K_of_coverInv (ModuleExclusions.coverInv_f4_charFive hECS Q hQ)
  | E6 => exact end415K_of_coverInv (ModuleExclusions.coverInv_e6_charFive hECS Q hQ)
  | E7 => exact end415K_of_coverInv (ModuleExclusions.coverInv_e7_charFive hECS Q hQ)
  | E8 => exact end415K_of_coverInv (ModuleExclusions.coverInv_e8_charFive hECS Q hQ)
  | twistedE6 =>
    exact end415K_of_coverInv (ModuleExclusions.coverInv_twistedE6_charFive hECS Q hQ)
  | trialityD4 => exact absurd (Or.inr ⟨rfl, hQ.1.2.1⟩) hpar
  | _ => exact absurd ht (by decide)

end CFSG.HardMathSupport.Foote.Coordinator
