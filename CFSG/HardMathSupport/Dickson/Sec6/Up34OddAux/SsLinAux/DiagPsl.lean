module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLin
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsLin

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.ComponentClassification.CatLeaf

theorem up34DiagPsl_of_hO (hO : LieOrderFormulasInput) : Up34DiagPsl := by
  intro n p f K _ _ hn3 hp hp5 _ hK ψ hψ3 hψD _
  exact noL34Layer_of_mem_linearAutGroup hO (by omega) hp hp5 hK hψD hψ3

end CFSG.HardMathSupport.Dickson.Sec6
