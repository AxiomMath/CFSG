module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUni
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutUni

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

namespace Up34Chev2

section Closed


theorem up34C2OutDiag_TwAHigh_holds : Up34C2OutDiag_TwAHigh := by
  intro n hn f K _ h _ _ ψ hψD _ hpump
  obtain ⟨A, rfl⟩ := hψD
  exact not_up34Pumpup_primeFormConjHom
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput h rfl hn A hpump

end Closed

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
