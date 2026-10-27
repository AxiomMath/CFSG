module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Main
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Final

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.AGLEmbedding (Asc81bEightFive)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (Asc81bEightTenPrinted)

theorem eightTenFourOutcome (h85 : Asc81bEightFive) :
    EightTenFourOutcome :=
  eightTenFourOutcome_of a7PerfectSylow h85

theorem asc81bEightTenPrinted_of_natural
    (h85 : GF2EightFive) (h94 : GF2NoFFTripleA7)
    (hnat : EightTenNaturalOnly) (h81 : Asc81bEightFive) : Asc81bEightTenPrinted :=
  asc81bEightTenPrinted_of_natural_and_four h85 h94 hnat (eightTenFourOutcome h81)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
