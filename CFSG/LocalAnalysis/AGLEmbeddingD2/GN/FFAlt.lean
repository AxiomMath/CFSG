module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def AGL81FiveThreeAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), IsKGroup X →
    CharTwo (⊤ : Subgroup X) → IsPGroup 2 T → pCoreOf 2 (⊤ : Subgroup X) ≤ T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      (Nonempty (↥L ≃* alternatingGroup (Fin 7)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T)) ∧
      (Nonempty (↥L ≃* alternatingGroup (Fin 6)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
        (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
            Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
          ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 4) ∧
      ((∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧
          d.1 = .twistedA 2 q) ∧ Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
        HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
        (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
            Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
          ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6)

end CFSG.AGLEmbeddingD2.GN
