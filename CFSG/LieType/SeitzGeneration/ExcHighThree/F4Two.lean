module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import Certificates.Certificate14950

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Final


theorem f4ThreeTwo_holds : F4ThreeTwo :=
  fun K _ _ hK E hE3 hE9 _ => Certificates.certificate14950 K hK E hE3 hE9

end Final

end CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two
