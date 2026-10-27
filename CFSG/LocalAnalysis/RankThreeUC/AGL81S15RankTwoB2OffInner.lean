module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Five
public import CFSG.RankThree.FFModules.Natural

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

section AGL

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem two_le_exponent_of_valid_B2 {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B 2 Q).Valid) : 2 ≤ Q.exponent := by
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hpos := Q.exponent_pos
  by_contra hlt
  have h1 : Q.exponent = 1 := by omega
  simp [hQ, h1] at hrange

end AGL

end CFSG.LocalAnalysis.RankThreeUC.S15

end
