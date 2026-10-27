module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Recognition
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.OfAlternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CGT.PushingUpLit.CGT6 CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

theorem stellmacherA5 :
    StellmacherA5 := by
  intro S _ _ hS _ Y hY _ hpair hA5
  exact stellmacherSixOneThree_of_A5Pair hS hY hpair hA5

theorem stellmacherSixOneThree_of_noA5
    (h0 : NoA5Branch) :
    StellmacherSixOneThree :=
  stellmacherSixOneThree_of_A5_noA5 stellmacherA5 h0

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
