module

public import CFSG.HardMathSupport.U4FF.ClassFinal
public import CFSG.HardMathSupport.U4FF.ClassClassifHolds
public import CFSG.HardMathSupport.U4FF.Natural4
public import CFSG.HardMathSupport.U4FF.Omega2Gen

public section

namespace CFSG.HardMathSupport.U4FF

theorem u4RankDichotomy_holds :
    U4RankDichotomy :=
  u4RankDichotomy_of_classif (fun _ _ _ _ _ hK => classif_holds hK) natural4Input_holds
    omega2InputGen_holds

end CFSG.HardMathSupport.U4FF
