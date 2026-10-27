module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnLinMain
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutLin

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.ComponentClassification.CatLeaf

namespace Up34Chev2

section Closed


theorem up34C2OutDiag_AHigh_holds : Up34C2OutDiag_AHigh :=
  fun _ hn _ _ _ _ _ hK A _ =>
    not_up34Pumpup_conjAut_psl CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hn
      hK A

end Closed

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
