module

public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatOdd
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatOdd

public section

namespace CFSG.SeitzReduction.CrossChar

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

section OrderFormulas

variable (hO : LieOrderFormulasInput)
include hO

theorem sLmNotOddLieInputAt_of_lieOrderFormulas {m : ℕ} (hm : m ≠ 2) :
    LinearPilot.SLmNotOddLieInputAt m := by
  intro X _ f hmf hX
  refine not_oddLieType_of_lieModel_two hO hX (fun h => hm h.2.1)
    (fun h => hmf (by rw [h.2.1, h.2.2])) (fun h => absurd h.1 (by decide))

theorem sUmNotOddLieInputAt_of_lieOrderFormulas (m : ℕ) : UnitaryPilot.SUmNotOddLieInputAt m := by
  intro X _ f hmf hX
  refine not_oddLieType_of_lieModel_two hO hX (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => hmf (by rw [h.2.1, h.2.2]))

variable (hGLS : GLS3OddLieAutComponentsInput)
include hGLS

theorem catSLmOddLieAt_of_lieOrderFormulas {m : ℕ} (hm : 3 ≤ m) :
    LinearPilot.CatSLmOddLieAt m :=
  LinearPilot.catSLmOddLieAt_of_inputs hGLS hm
    (sLmNotOddLieInputAt_of_lieOrderFormulas hO (by omega))

end OrderFormulas

end CFSG.SeitzReduction.CrossChar
