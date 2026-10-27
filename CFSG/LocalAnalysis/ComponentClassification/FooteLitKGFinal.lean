module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGAlt
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGSpor
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ1
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ3
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGM12
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGEven

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG.ComponentClassification.FooteLit.KG

theorem foote5KnownGroups_holds :
    Foote5.Foote5KnownGroups :=
  foote5KnownGroups_of footeKnownQuot_alt9 footeKnownQuot_alt10 footeKnownQuot_alt11
    footeKnownQuot_J2 (fun G _ _ _ h => footeKnownSmall_L28 G h)
    (fun G _ _ _ h => footeKnownSmall_L216 G h) (fun G _ _ _ h => footeKnownSmall_L34 G h)
    (fun G _ _ _ h => footeKnownSmall_Sz8 G h)
    (fun G _ _ h => FooteKnownSmall.of_no (noFooteComponent_alt8 G h))
    (fun G _ _ _ h => footeKnownSmall_M12 G h)
    (fun G _ _ _ h => FooteKnownSmall.of_no (noFooteComponent_M22 G h))
    (fun G _ _ _ h => FooteKnownSmall.of_no (noFooteComponent_M23 G h))
    (fun G _ _ _ h => footeKnownSmall_J1 G h) (fun G _ _ _ h => footeKnownSmall_J3 G h)
    (fun G _ _ _ h => FooteKnownSmall.of_no (noFooteComponent_McL G h))
    (fun G _ _ _ h => FooteKnownSmall.of_no (noFooteComponent_Ly G h))

end CFSG.ComponentClassification.FooteLit
