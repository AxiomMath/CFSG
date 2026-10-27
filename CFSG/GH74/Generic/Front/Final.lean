module

public import CFSG.GH74.Generic.Front.S2
public import CFSG.GH74.Generic.Front.OuterThree
public import CFSG.GH74.Generic.Front.DataStatement
public import CFSG.GH74.Generic.Front.SpOuter

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

theorem s2_shapeCase_proved : S_shapeCase @ShapeS2 :=
  s2_shapeCase frontDataStatement (outerStatement_of_three outerThreeStatement) spOuterInvolution

theorem s_generic_of_shapes_S1_S3_S4_S5
    (hF : GenericKnownFacts)
    (h1 : S_shapeCase @ShapeS1) (h3 : S_shapeCase @ShapeS3) (h4 : S_shapeCase @ShapeS4)
    (h5 : S_shapeCase @ShapeS5) : S_generic' :=
  s_generic_of_shape_cases hF h1 s2_shapeCase_proved h3 h4 h5

end CFSG.GH74.Generic
