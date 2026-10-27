module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.RankThreeCoreUniqueness.Helpers

structure CaseBG0 {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)
    (G₁ G₂ S₀ W₁ W₂ : Subgroup G) : Prop where
  swap : ∀ x : G, x ∈ G₂ ↔ d.t⁻¹ * x * d.t ∈ G₁
  comm : ⁅G₁, G₂⁆ = ⊥
  perfect : ⁅G₁, G₁⁆ = G₁
  model : LieModel (G₁ ⧸ center G₁) .PSL 3 2 2
  odd_centralizer : Odd (Nat.card (centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)))
  S₀_le : S₀ ≤ G₁ ⊔ G₂
  card_S₀ : Nat.card S₀ = 2 ^ 12
  W₁_le : W₁ ≤ S₀
  W₂_le : W₂ ≤ S₀
  W₁_elem : IsElemAbelian 2 W₁
  W₂_elem : IsElemAbelian 2 W₂
  card_W₁ : Nat.card W₁ = 2 ^ 8
  card_W₂ : Nat.card W₂ = 2 ^ 8
  W_sup : W₁ ⊔ W₂ = S₀
  G₀_eq : G₁ ⊔ G₂ =
    perfectResidualOf (normalizer (W₁ : Set G)) ⊔ perfectResidualOf (normalizer (W₂ : Set G))
  P_le : d.P ≤ normalizer (S₀ : Set G)
  qmax₁ : ∀ Q : Subgroup G, Q ≤ perfectResidualOf (normalizer (W₁ : Set G)) → ⁅Q, Q⁆ = Q →
    S₀ ≤ Q → Q = perfectResidualOf (normalizer (W₁ : Set G))
  qmax₂ : ∀ Q : Subgroup G, Q ≤ perfectResidualOf (normalizer (W₂ : Set G)) → ⁅Q, Q⁆ = Q →
    S₀ ≤ Q → Q = perfectResidualOf (normalizer (W₂ : Set G))
  loc : ∀ W : Subgroup G, W ≤ S₀ → IsElemAbelian 2 W → Nat.card W = 2 ^ 8 →
    S₀ ≤ perfectResidualOf (normalizer (W : Set G) ⊓ (G₁ ⊔ G₂))

end CFSG.OddStandard.Seitz77
