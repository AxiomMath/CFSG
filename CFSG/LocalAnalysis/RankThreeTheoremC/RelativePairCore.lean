module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactOuterSylowInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (p : ℕ) [Fact p.Prime], p ≠ 2 →
    IsComponentOf L ⊤ → IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → p ∣ Nat.card L →
    ∀ S : Subgroup Y, S ≤ L → IsPGroup p S → ¬ p ∣ (S.subgroupOf L).index → IsCyclic S →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 → (∀ s ∈ S, x * s = s * x) →
      x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

end CFSG.LocalAnalysis.RankThreeTheoremC
