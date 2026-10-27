module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.FFAlt

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem a6_clause {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (eL : ↥L ≃* alternatingGroup (Fin 6)) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
      (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 4 := by
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  obtain ⟨A, hA, hAN, hLA⟩ := exists_offender_of_le hV hVT L hL hJ
  exact a6_clause_of_offender hV L eL hA (isBestOffender_gnRep_of_le hV hVT hA) hAN hLA

@[expose] def AGL81FiveThreeRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), CFSG.IsKGroup X →
    CharTwo (⊤ : Subgroup X) → IsPGroup 2 T → pCoreOf 2 (⊤ : Subgroup X) ≤ T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      (Nonempty (↥L ≃* alternatingGroup (Fin 7)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T)) ∧
      ((∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
          d.1 = .twistedA 2 q) ∧ Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
        (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
            Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
          ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6)

theorem agl81FiveThreeAlt_of_rest (h : AGL81FiveThreeRest) : GN.AGL81FiveThreeAlt := by
  intro X _ _ T hK hC hT2 hQT L hL hJ
  obtain ⟨h7, hU⟩ := h X T hK hC hT2 hQT L hL hJ
  exact ⟨h7, fun ⟨e⟩ => a6_clause T hC hQT L hL hJ e, hU⟩

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
