module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Clause

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

@[expose] def AGL81FiveThreeU33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), CFSG.IsKGroup X →
    CharTwo (⊤ : Subgroup X) → IsPGroup 2 T → pCoreOf 2 (⊤ : Subgroup X) ≤ T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ((∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
          d.1 = .twistedA 2 q) ∧ Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
        (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
            Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
          ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6)

theorem agl81FiveThreeRest_of_u33 (h : AGL81FiveThreeU33) : AGL81FiveThreeRest := by
  intro X _ _ T hK hC hT2 hQT L hL hJ
  exact ⟨fun ⟨e⟩ => a7_clause T hC hQT L hL hJ e, h X T hK hC hT2 hQT L hL hJ⟩

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
