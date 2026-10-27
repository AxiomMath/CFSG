module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepOffenderJ
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541EvenAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

theorem exists_strictMin_offender_of_gn_component {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hGN : GNSetting X T) (hV : IsElemAbelian 2 (gnV T))
    [Module (ZMod 2) (Additive (IntMod (gnV T) hV))] {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ B : Subgroup (X ⧸ gnC T), B ≤ gnImg T (thompsonJ T) ∧
      (∀ b ∈ B, b * b = 1) ∧ (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) ∧
      (∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) ∧
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) (L ⊔ B) (commOn (gnRep hV) L ⊤) ∧
      ¬ L ≤ cenOn (gnRep hV) L (commOn (gnRep hV) L ⊤) ∧
      ¬ B ≤ cenOn (gnRep hV) B (commOn (gnRep hV) L ⊤) ∧
      IsBestOffenderOn (gnRep hV) B (commOn (gnRep hV) L ⊤) ∧
      IsQuadraticOn (gnRep hV) B (commOn (gnRep hV) L ⊤) ∧
      ∀ b ∈ B, b ∉ cenOn (gnRep hV) B (commOn (gnRep hV) L ⊤) →
        ∃ k ∈ L, ∃ u ∈ commOn (gnRep hV) L ⊤,
          gnRep hV b (gnRep hV k u) ≠ gnRep hV k (gnRep hV b u) := by
  obtain ⟨A, hA2, hAb, hAN, hLA, hAJ⟩ := exists_rep_offender_J hGN hV hL hJ
  have hinj := gnRep_injective hV
  have hfaith : ∀ a ∈ A, (∀ v, gnRep hV a v = v) → a = 1 := fun a _ h =>
    hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn (gnRep hV) A ⊤ := (isBestOffender_iff_on _ A hfaith).mp ⟨hA2, hAb⟩
  have hKnt : ¬ L ≤ cenOn (gnRep hV) L ⊤ := by
    intro hle
    apply ne_bot_of_isComponentOf hL
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    exact LinearMap.ext fun v => (mem_cenOn.mp (hle hl)).2 v Submodule.mem_top
  obtain ⟨B, hBA, hinvB, hLnt, hBnt, hbestB, hquadB, hmove, -⟩ :=
    exists_strictMin_moving L A hA2 hAN hLA hKnt hb
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) b (hBA hb)
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have := hA2.toIsMulCommutative.is_comm.comm ⟨b, hBA hb⟩ ⟨c, hBA hc⟩
    exact congrArg Subtype.val this
  have hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAN (hBA hb)) l).mp hl
  exact ⟨B, hBA.trans hAJ, hB2, hBc, hBN, hinvB, hLnt, hBnt, hbestB, hquadB, hmove⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
