module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5.Branch
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StellmacherA5

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

theorem stellmacherSixOneThree_holds :
    CFSG.CGT.PushingUpLit.CGT6.StellmacherSixOneThree :=
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.stellmacherSixOneThree_of_noA5
    noA5Branch

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
