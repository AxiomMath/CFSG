module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Dichotomy
import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepATw

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis (repA repD)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


theorem e6HeisFrameFixedElt_of_classD (hD : E6HeisFrameFixedEltD) : E6HeisFrameFixedElt :=
  e6HeisFrameFixedElt_of_classes e6HeisFrameFixedEltA_holds hD

theorem twE6HeisFrameFixedElt_of_classD (hD : TwE6HeisFrameFixedEltD) : TwE6HeisFrameFixedElt :=
  twE6HeisFrameFixedElt_of_classes twE6HeisFrameFixedEltA_holds hD

end CFSG.LieType.SeitzGeneration.ExcWideThree
