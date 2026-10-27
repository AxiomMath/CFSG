module

public import CFSG.Sporadic.Th.Certificate
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Blueprint Blueprint.NativeSporadic Assembly.LowTwoRank

theorem card_nativeTh : Nat.card NativeSporadic.Th = 90745943887872000 :=
  Sporadic.Th.card_nativeTh_kernel

end CFSG.ComponentClassification.UnbalancedCorr
