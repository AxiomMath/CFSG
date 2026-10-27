module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Tw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Class

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

section Holds

theorem l154OmegaNID_exc_holds : L154OmegaNID l154Exc :=
  l154OmegaNID_exc l154OmegaNID_excRee_holds

theorem l154OmegaTD4_exc_of_td4Class (hC : L154TD4Class) : L154OmegaTD4 l154Exc :=
  l154OmegaTD4_exc_of_class hC l154OmegaTD4_excRee

theorem l154OmegaTD4_exc_holds : L154OmegaTD4 l154Exc :=
  l154OmegaTD4_exc_of_td4Class l154td4_class_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
