module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Order62
public import CFSG.Sporadic.Th.Max3.AllConjFinal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint

section Th


theorem noOrder186_Th : NoOrder 186 NativeSporadic.Th :=
  noOrder186_Th_of_card fun w hw => by
    rw [card_centralizer_of_isConj (CFSG.Sporadic.Th.Max3.all_involutions_conjugate w hw),
      CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts,
      CFSG.Sporadic.Th.Max3.card_M]

end Th

end CFSG.HardMathSupport.Dickson.Sec6.I1431
