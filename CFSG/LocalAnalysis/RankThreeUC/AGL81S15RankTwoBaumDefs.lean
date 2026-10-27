module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

@[expose] def K517_4b_thompsonJ_A2B2G2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      (∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .G2 Q) →
      IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        gnImg T (CFSG.Quasithin.thompsonJ T) ≤
          Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))

@[expose] def K517_4b_baumPower_A2B2G2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      (∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .G2 Q) →
      IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
          ∀ x ∈ Ls ⊓ Subgroup.normalizer
              ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)),
            s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls

end CFSG.LocalAnalysis.RankThreeUC.S15

end
