module

public import CFSG.HardMathSupport.Foote.E27.Remaining

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

set_option linter.unusedSectionVars false

open CFSG.HardMathSupport.Foote.E27

theorem kFactMSideAlmostSimpleE27_proved : CFSG.AGLEmbedding.KFactMSideAlmostSimpleE27 :=
  CFSG.HardMathSupport.Foote.E27.kFactMSideAlmostSimpleE27_of_two_cells
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.innerLeaf_E6_two
    CFSG.HardMathSupport.Curtis.UnitaryLevi.innerLeaf_twistedE6_one

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
