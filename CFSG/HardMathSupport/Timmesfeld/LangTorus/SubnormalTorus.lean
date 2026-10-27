module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped commutatorElement
open Matrix

set_option linter.unusedSectionVars false


theorem langSubnormal_provedT : LangSubnormalT := fun _ _ _ _ _ S _ hdT _ _ i =>
  langSubnormal_of_mem_torus S hdT i

end CFSG.HardMathSupport.Timmesfeld.LangTorus
