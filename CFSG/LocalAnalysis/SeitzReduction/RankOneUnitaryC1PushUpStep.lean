module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpConf

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def U3C1OuterMoveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    (∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) → U3C1Cartan L T D d →
    U3C1OuterConf G L f t T R₂ D V k → 2 ≤ k → (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V) →
    ∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G), ∃ r ∈ V, (∀ x ∈ V, x ^ 2 ≠ r) ∧
      y * t * y⁻¹ = r * t

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem eq_of_one (hc : U3C1OuterConf G L f t T R₂ D V 1) (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    V = R₂ :=
  (eq_of_le_of_card_ge hc.R₂_le (by rw [hc.card, hR.card])).symm

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
