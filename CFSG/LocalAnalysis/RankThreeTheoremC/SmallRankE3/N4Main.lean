module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4KGPre
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Large

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

@[expose] def SlotP614GammaE3U0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G → ∀ (p : ℕ),
    5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M →
          (∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
            ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
          IsPGroup 2 (rankThreePrimeCore p H) → ¬ HasPrimeConstraint (G := M) p → False

@[expose] def SlotP614GammaFieldAutE3U0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G → ∀ (p : ℕ), 5 ≤ p →
    ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z →
        ∀ H S L : Subgroup G, Fail614OptimalGen p M x z H S → rankThreePrimeCore p H ≤ M →
          IsPGroup 2 (rankThreePrimeCore p H) → ¬ HasPrimeConstraint (G := M) p →
          KGData3Pre p H (rankThreePrimeCore p H) S (zpowers x ⊔ zpowers z) L M z →
          (∀ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z →
            ¬ ((∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ rankThreePrimeCore p H) ∧
              (∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ rankThreePrimeCore p H))) → False

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
