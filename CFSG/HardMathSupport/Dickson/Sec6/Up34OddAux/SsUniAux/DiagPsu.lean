module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsUni
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLin

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Dickson.Sec6.I923

theorem up34DiagPsu_of_lieOrderFormulas (hO : LieOrderFormulasInput) : Up34DiagPsu := by
  intro n p f K _ h hn hp5 ψ hψ3 hψD _
  exact noL34Layer_of_mem_primeFormD hO h hp5 hn hψD hψ3

end CFSG.HardMathSupport.Dickson.Sec6
