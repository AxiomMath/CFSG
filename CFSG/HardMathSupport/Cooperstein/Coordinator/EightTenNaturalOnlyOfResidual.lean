module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNaturalOfResidual
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Main

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour (EightTenNaturalOnly)

theorem eightTenNaturalOnly_of_residual (hnat : GF2NaturalLSL)
    (hres : EightTenResidualOutcomes) : EightTenNaturalOnly :=
  fun G _ _ X S L hX hA hL hSL m hm he hN =>
    eightTen_natural_of_residual hnat hres G X S L hX hA hL hSL m hm he hN

end CFSG.HardMathSupport.Cooperstein.Coordinator
