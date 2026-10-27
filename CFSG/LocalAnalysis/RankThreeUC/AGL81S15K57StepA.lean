module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

@[expose] def K541CountEven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, 0 < n → Even n →
        Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) →
        ∀ P₀ P₁ P₂ P₃ : Subgroup X, P₀ < P₁ → P₁ < P₂ → P₂ < P₃ → P₃ ≤ gnV T →
          Ls.comap (toStar T) ≤ Subgroup.normalizer (P₀ : Set X) →
          Ls.comap (toStar T) ≤ Subgroup.normalizer (P₁ : Set X) →
          Ls.comap (toStar T) ≤ Subgroup.normalizer (P₂ : Set X) →
          Ls.comap (toStar T) ≤ Subgroup.normalizer (P₃ : Set X) →
          ⁅P₁, Ls.comap (toStar T)⁆ ≤ P₀ ∨ ⁅P₂, Ls.comap (toStar T)⁆ ≤ P₁ ∨
            ⁅P₃, Ls.comap (toStar T)⁆ ≤ P₂

end CFSG.LocalAnalysis.RankThreeUC.S15
