module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeNode
public import CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineReduction
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortNode

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

theorem chevNoAlt_of_open
    (hbad : EightNineNonParabolic) (h883 : EightEightShort) : Asc81bNineThreeChevNoAlt :=
  chevNoAlt_of_nodes (eightNine_of_nonParabolic hbad) eightEightShapeNoAlt h883

theorem chevNoAlt_of_nonParabolic
    (hbad : EightNineNonParabolic) : Asc81bNineThreeChevNoAlt :=
  chevNoAlt_of_open hbad eightEightShort

end CFSG.HardMathSupport.Cooperstein.StructureLie
