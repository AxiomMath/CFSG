module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.AppC (C56DoubleNonA3 c56DoubleCase_of not_alt3_of_alt5 not_lin2_of_alt5)

theorem c56DoubleCase_of_nonA3 (ho : C56DoubleNonA3) : C56DoubleCase :=
  c56DoubleCase_of c56DoubleA3 ho

end CFSG.QuasithinUnique.AppD
