module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Fail614NormalizerRank (P : Sylow 3 G) (M B : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsMaxTwoInvariantIn B M T →
    CFSG.Open.pRank 3 (P : Subgroup G) ≤ CFSG.Open.pRank 3 (M ⊓ normalizer (T : Set G))

structure Fail614Optimal (M : Subgroup G) (x z : G) (H S : Subgroup G) : Prop where
  ext : Prop614Extremal M (zpowers x ⊔ zpowers z) H S
  eq_normalizer : H = normalizer (pCoreOf 2 H : Set G)
  maxInv : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S
  core_le : pCoreOf 2 H ≤ S
  norm_le : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
    S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M
  pRank_le : CFSG.Open.pRank 3 H ≤ 2
  sylow_le : ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ H → zpowers x ⊔ zpowers z ≤ Q → Q ≤ M

@[expose] def Prop614FailCore (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
    (HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Fail614Optimal M x z H S → rankThreePrimeCore 3 H ≤ M → False

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
