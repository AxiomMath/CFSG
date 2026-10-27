module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ARuTwo

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

namespace L32A

variable {G : Type} [Group G]

section Setting

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem fsuU_eq_conjClosure_hz_F4 (hMod : StmtL32NModule_F4) (h : Hyp147 G T L V) :
    fsuU T V = conjClosure V (L32A.hz T V) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  show conjClosure V (Subgroup.normalizer (fsuV1 T V : Set G)) = _
  rw [normalizer_eq_centralizer_of_card_two hV1]

end Setting

end L32A

end CFSG.Quasithin.H13
