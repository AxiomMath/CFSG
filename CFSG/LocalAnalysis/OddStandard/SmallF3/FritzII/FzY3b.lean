module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL42
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzSNotSylowCtx_holds :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
      (x₁ x₂ lam rho tau : G), Ctx t L S x₁ x₂ lam rho tau → 2 ∣ S.index := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau h
  have hS : 2 ^ 6 ∣ Nat.card S := ⟨Nat.card (twoCore t), h.card_S⟩
  have h4 : 4 ∣ Nat.card G :=
    ((by norm_num : 4 ∣ 2 ^ 6).trans hS).trans (Subgroup.card_subgroup_dvd_card S)
  exact S4A.lemma4_2_of_simple ‹IsSimpleGroup G› h4 h

theorem fzCardTwoCoreCtx_holds :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
      (x₁ x₂ lam rho tau : G), Ctx t L S x₁ x₂ lam rho tau →
      Nat.card (twoCore t) = 2 ∨ Nat.card (twoCore t) = 4 := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau h
  have h2 : 2 ∣ S.index := fzSNotSylowCtx_holds G t L S x₁ x₂ lam rho tau h
  rcases S4A.card_twoCore_cases h.hyp with h2c | h4c | h8
  · exact Or.inl h2c
  · exact Or.inr h4c
  · exact (S4A.false_of_eight_le_card h h2 h8).elim

end CFSG.OddStandard.SmallF3.FritzII
