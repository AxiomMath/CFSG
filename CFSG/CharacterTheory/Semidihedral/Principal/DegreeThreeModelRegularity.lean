module

public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeThreeModelRegularitySupport

public section

namespace CFSG.Semidihedral.Principal

open CFSG.Assembly.LowTwoRank CFSG.Semidihedral.Principal.DegreeThreeModel
  CFSG.Wreathed.OddLinearThreeCentralizerCore

theorem degree_three_model_characteristic_valuation_regularity {G : Type} [Group G]
    (τ : StatedLieTag) (hτ : τ = .PSL ∨ τ = .PSU) (p f : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (hmodel : StatedClassicalModel G τ 3 p f) :
    Finite G ∧ padicValNat p (Nat.card G) = 3 * f ∧
      (∀ t : G, orderOf t = 2 →
        padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) = f) ∧
      ∀ t s : G, orderOf t = 2 → orderOf s = 2 →
        3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
            2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
              Subgroup.centralizer ({s} : Set G) : Subgroup G)) : ℤ) ≤
          padicValNat p (Nat.card G) := by
  have : Fact p.Prime := ⟨hp⟩
  have key : Finite G ∧ padicValNat p (Nat.card G) = 3 * f ∧
      ∀ t : G, orderOf t = 2 →
        padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) = f := by
    rcases hτ with rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
      let e' : G ≃* (SL3 K ⧸ Subgroup.center (SL3 K)) :=
        e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
      refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_, fun t ht => ?_⟩
      · rw [Nat.card_congr e.toEquiv, padicValNat_card_psl3 hp hf hK]
      · rw [← card_centralizer_mulEquiv e' t]
        exact padicValNat_centralizer_psl3 hp hpodd hf hK (e' t)
          (by rw [MulEquiv.orderOf_eq]; exact ht)
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
      refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_, fun t ht => ?_⟩
      · rw [Nat.card_congr e.toEquiv, padicValNat_card_psu3 hf hK]
      · rw [← card_centralizer_mulEquiv e t]
        exact padicValNat_centralizer_psu3 hpodd hf hK (e t)
          (by rw [MulEquiv.orderOf_eq]; exact ht)
  obtain ⟨hfin, hG, hC⟩ := key
  refine ⟨hfin, hG, hC, fun t s ht _ => ?_⟩
  rw [hC t ht, hG]
  have h0 : (0 : ℤ) ≤ (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({s} : Set G) : Subgroup G)) : ℤ) := Nat.cast_nonneg _
  have h3 : ((3 * f : ℕ) : ℤ) = 3 * (f : ℤ) := by push_cast; ring
  rw [h3]
  linarith

end CFSG.Semidihedral.Principal
