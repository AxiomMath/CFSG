module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure Setup65A (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G) :
    Prop where
  setting : Setting G
  u0 : FullCoreLocal G
  situation : SmallRankSituation G 3 P M
  constrained : HasPrimeConstraint (G := M) 3
  point : SmallRankPoint P M x
  central : SmallRankCentral P z

@[expose] def GL83SmallRankProp65Alpha (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
    HasPrimeConstraint (G := M) 3 →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ F : Subgroup G, F ≤ M → F ≠ ⊥ → Nat.Coprime (Nat.card F) 6 →
        zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
