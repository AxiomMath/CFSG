module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S14612DA
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Input14615ContraOuterP_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
              CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → ¬ K₁ ≤ J → False

@[expose] def Input14615ContraInnerP_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
              CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → K₁ ≤ J → False

end CFSG.Quasithin
