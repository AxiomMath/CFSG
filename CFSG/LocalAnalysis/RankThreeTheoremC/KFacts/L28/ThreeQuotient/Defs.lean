module

public import CFSG.Open.Defs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)

@[expose] def Sylow3OmegaLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → (∃ (t : StatedLieTag) (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f ∧
      LieModel K t n ℓ f) → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 →
    ∀ S : Sylow 3 K, Nat.card S = 3 ^ 5 →
      (∀ x ∈ (S : Subgroup K), ∀ y ∈ (S : Subgroup K), x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x) →
        IsMulCommutative (S : Subgroup K)

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
