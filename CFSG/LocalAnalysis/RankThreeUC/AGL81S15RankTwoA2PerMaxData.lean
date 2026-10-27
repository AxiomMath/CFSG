module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoA2Inner
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open Matrix
open scoped commutatorElement MatrixGroups

section AGL

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem isBestOffenderOn_gnImg (hGN : GNSetting X T) (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]
    {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    IsBestOffenderOn (gnRep hV) (gnImg T A) ⊤ := by
  have hfaith : ∀ a ∈ gnImg T A, (∀ v : gnW T hV, gnRep hV a v = v) → a = 1 := by
    intro a _ hv
    apply gnRep_injective hV
    rw [map_one]
    exact LinearMap.ext fun v => by simpa using hv v
  have hel : CFSG.IsElementaryAbelian 2 ↥(gnImg T A) := by
    unfold gnImg
    exact isElementaryAbelian_map_mk (T := T) (A := A) hA
  have hbest : IsBestOffender (gnRep hV) (gnImg T A) := by
    simpa [gnImg] using isBestOffender_gnRep (T := T) hV hGN hA
  exact (isBestOffender_iff_on (gnRep hV) (gnImg T A) hfaith).mp ⟨hel, hbest⟩

end AGL

end CFSG.LocalAnalysis.RankThreeUC.S15
