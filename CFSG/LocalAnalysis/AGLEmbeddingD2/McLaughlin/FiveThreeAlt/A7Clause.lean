module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Module
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
open scoped commutatorElement

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem a7_clause_of_offender [Finite X] (L : Subgroup (X ⧸ gnC T))
    (eL : ↥L ≃* alternatingGroup (Fin 7)) {A : Subgroup X} (hA : IsMaxElemAbelian T A)
    (hAb : IsBestOffender (gnRep hV) (A.map (QuotientGroup.mk' (gnC T))))
    (hAN : A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hLA : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) := by
  classical
  set ρ := gnRep hV with hρ
  set L' := L.comap (QuotientGroup.mk' (gnC T)) with hL'
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hA2 := isElementaryAbelian_map_mk hA
  have hfaith : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ hfaith).mp ⟨hA2, hAb⟩
  obtain ⟨hirr, hlt⟩ := a7_commOn_quot ρ hinj eL hA2 hAN hLA hb
  set U := commOn ρ L ⊤ with hU
  set C := fixOn ρ L U with hC
  have hUs : subOf hV U = ⁅gnV T, L'⁆ := subOf_commOn hV L
  have hCs : subOf hV C = ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
    rw [hC, subOf_fixOn, hUs]
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  refine ⟨?_, fun W' hW1 hW2 hW3 => ?_⟩
  · rw [← hCs, ← hUs]
    refine lt_of_le_of_ne ((subOf_le_subOf_iff hV).mpr hCU) fun h => ?_
    exact hlt.not_ge ((subOf_le_subOf_iff hV).mp h.ge)
  · rw [← hCs] at hW1
    rw [← hUs] at hW2
    rw [← hCs, ← hUs]
    have hW'V : W' ≤ gnV T := hW2.trans (subOf_le_gnV hV U)
    have hinv := isInvariant_modOf hV L hW3
    have h1 : C ≤ modOf hV W' := by
      rw [← modOf_subOf hV C]
      intro w hw
      exact hW1 hw
    have h2 : modOf hV W' ≤ U := by
      rw [← modOf_subOf hV U]
      intro w hw
      exact hW2 hw
    rcases hirr _ hinv h1 h2 with h | h
    · left
      rw [← h, subOf_modOf hV hW'V]
    · right
      rw [← h, subOf_modOf hV hW'V]

theorem a7_clause {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (eL : ↥L ≃* alternatingGroup (Fin 7)) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) := by
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  obtain ⟨A, hA, hAN, hLA⟩ := exists_offender_of_le hV hVT L hL hJ
  exact a7_clause_of_offender hV L eL hA (isBestOffender_gnRep_of_le hV hVT hA) hAN hLA

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
