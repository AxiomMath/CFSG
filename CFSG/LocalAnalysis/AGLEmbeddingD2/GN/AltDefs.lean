module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.C1GNDefs

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GNAltFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
      ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T C₁ C₂ L →
        ∀ n : ℕ, (n = 7 ∨ 8 < n) →
          Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)) →
            Subgroup.center ↥L = ⊥ ∧
            ¬ pElementSubgroup 3 (gnA T C₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
            ((8 < n ∨ gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))) →
              1 < Open.pRank 3 (gnA T C₁ L) ∨ 1 < Open.pRank 3 (gnA T C₂ L))

end CFSG.AGLEmbeddingD2.GN
