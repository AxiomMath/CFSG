
module


public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Classify
public import Certificates.Certificate134003

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Equiv Equiv.Perm CFSG.Open CFSG.Quasithin

theorem a7Good_of_radical (hA7 : IsSimpleGroup A7) {P : Subgroup A7} (hrad : IsTwoRadicalIn ⊤ P) :
    A7Good P :=
  Certificates.certificate134003 hA7 P hrad

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
