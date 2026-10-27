module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def GL83SmallRankProp614Sylow (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        (∃ S : Subgroup G, S ≤ H ⊓ M ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
          zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) → H ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC
