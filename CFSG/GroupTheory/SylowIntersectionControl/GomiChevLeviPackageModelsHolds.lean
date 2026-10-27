module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviModelsExcHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviModelsSmallHolds
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.PSLType
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorsSL
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviModelsClassical

public section

namespace CFSG.GroupTheory

open CFSG.Open

theorem gomiChevLeviPackageModel_holds
    (hSp : GomiLeviFactorsSp) (hSU : GomiLeviFactorsSU) (hSpinPlus : GomiLeviFactorsSpinPlus)
    (hSpinMinus : GomiLeviFactorsSpinMinus) (hF4 : GomiLeviFactorsF4) (hE6 : GomiLeviFactorsE6)
    (hE7 : GomiLeviFactorsE7) (hE8 : GomiLeviFactorsE8) (hE6tw : GomiLeviFactorsTwistedE6)
    (t : StatedLieTag) (n : ℕ) (ht : t ≠ .Tits) : GomiChevLeviPackageModel t n := by
  have hSL : GomiLeviFactorsSL :=
    gomiLeviFactorsSL_of_isChevTwo fun G _ k f h =>
      CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isChevTwo_of_classicalTwoOrG2
        (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isClassicalTwoOrG2_of_statedPSL h)
  cases t
  · exact gomiChevLeviPackageModel_classical hSL hSp hSU hSpinPlus hSpinMinus (by decide) n
  · exact gomiChevLeviPackageModel_classical hSL hSp hSU hSpinPlus hSpinMinus (by decide) n
  · exact gomiChevLeviPackageModel_classical hSL hSp hSU hSpinPlus hSpinMinus (by decide) n
  · exact gomiChevLeviPackageModel_pOmegaOdd n
  · exact gomiChevLeviPackageModel_classical hSL hSp hSU hSpinPlus hSpinMinus (by decide) n
  · exact gomiChevLeviPackageModel_classical hSL hSp hSU hSpinPlus hSpinMinus (by decide) n
  · exact gomiChevLeviPackageModel_g2 n
  · exact gomiChevLeviPackageModel_f4 hF4 n
  · exact gomiChevLeviPackageModel_e6 hE6 n
  · exact gomiChevLeviPackageModel_e7 hE7 n
  · exact gomiChevLeviPackageModel_e8 hE8 n
  · exact gomiChevLeviPackageModel_twistedE6 hE6tw n
  · exact gomiChevLeviPackageModel_trialityD4 n
  · exact gomiChevLeviPackageModel_twistedB2 n
  · exact gomiChevLeviPackageModel_twistedG2 n
  · exact gomiChevLeviPackageModel_twistedF4 n
  · exact absurd rfl ht

end CFSG.GroupTheory
