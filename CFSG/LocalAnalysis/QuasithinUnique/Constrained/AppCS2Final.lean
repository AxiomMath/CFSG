module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Seven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDFinal

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.QuasithinUnique

theorem c56DoubleNonA3 : AppC.C56DoubleNonA3 := AppE.c56DoubleNonA3 c56DoubleA5

theorem c56DoubleCase : C56DoubleCase := AppD.c56DoubleCase_of_nonA3 c56DoubleNonA3

end CFSG.QuasithinUnique.AppCS2
