module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Final81a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
    (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → Nat.card ↥S = 2 ^ 7 →
      Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
        (∃ Sg : Subgroup G, Concl810 S K₁ W₂ h t Sg) → ∀ v : G, orderOf v = 2 → IsConj z v

@[expose] def Final81b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
    (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → Nat.card ↥S = 2 ^ 7 →
      Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
        (∃ Sg : Subgroup G, Concl810 S K₁ W₂ h t Sg) →
        ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧
          ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f)) ∧
          (∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))) ∧
          ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
            ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
              (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
                  (centralizer ({z'} : Set Gs)).subtype →
                Nonempty (↥(layerSBar z S) ≃* ↥(layerSBar z' (S'' : Subgroup Gs)))

theorem final81_of_a_b (ha : Final81a) (hb : Final81b) : Final81 := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS128 hC E₁ E₂ hE hSg
  exact And.intro (ha G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS128 hC E₁ E₂ hE hSg)
    (hb G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS128 hC E₁ E₂ hE hSg)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
