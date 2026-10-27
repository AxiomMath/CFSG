module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.ComponentClassification.HarrisLit

private theorem card_of_isSLTwoOver {q : ℕ} {A : Type} [Group A] (h : IsSLTwoOver q A) :
    Nat.card A = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_eq_fintype_card, hF]

private theorem two_le_of_isSLTwoOver {q : ℕ} {A : Type} [Group A] (h : IsSLTwoOver q A) :
    2 ≤ q := by
  obtain ⟨F, _, _, hF, _⟩ := h
  have : 1 < Fintype.card F := Fintype.one_lt_card
  omega

private theorem mul_sq_sub_one_eq (n : ℕ) : n * (n ^ 2 - 1) = n * (n - 1) * (n + 1) := by
  have h : n ^ 2 - 1 = (n + 1) * (n - 1) := by
    simpa using Nat.sq_sub_sq n 1
  rw [h, mul_comm (n + 1) (n - 1), ← mul_assoc]

private theorem mul_sq_sub_one_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have hsub : a - 1 < b - 1 := by omega
  have hb1 : 0 < b - 1 := by omega
  have ha0 : 0 < a := by omega
  have ha1 : 0 < a - 1 := by omega
  have hAB : a * (a - 1) < b * (b - 1) :=
    mul_lt_mul_of_pos hab hsub ha0 hb1
  have hprod : a * (a - 1) * (a + 1) < b * (b - 1) * (b + 1) :=
    mul_lt_mul_of_pos hAB (Nat.add_lt_add_right hab 1) (Nat.mul_pos ha0 ha1) (Nat.succ_pos b)
  rw [mul_sq_sub_one_eq a, mul_sq_sub_one_eq b]
  exact hprod

theorem isSLTwoOver_unique {Y : Type} [Group Y] {q q' : ℕ} (h : IsSLTwoOver q Y)
    (h' : IsSLTwoOver q' Y) : q = q' := by
  have hq := two_le_of_isSLTwoOver h
  have hq' := two_le_of_isSLTwoOver h'
  have hcard : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1) := by
    rw [← card_of_isSLTwoOver h, ← card_of_isSLTwoOver h']
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd hcard (ne_of_lt (mul_sq_sub_one_lt hq hlt))
  · exact heq
  · exact absurd hcard.symm (ne_of_lt (mul_sq_sub_one_lt hq' hgt))

theorem pumpup_cases_of_isSLTwoOver {Y : Type} [Group Y] {p k : ℕ} {A B C : Prop}
    (hY : IsSLTwoOver (p ^ k) Y)
    (h : (p = 7 ∧ IsSLTwoOver 7 Y ∧ A) ∨ (p = 5 ∧ IsSLTwoOver 5 Y ∧ B) ∨
      (p = 3 ∧ IsSLTwoOver 9 Y ∧ C)) :
    (p = 7 ∧ k = 1 ∧ A) ∨ (p = 5 ∧ k = 1 ∧ B) ∨ (p = 3 ∧ k = 2 ∧ C) := by
  rcases h with ⟨rfl, h7, hA⟩ | ⟨rfl, h5, hB⟩ | ⟨rfl, h9, hC⟩
  · have hk : 7 ^ k = 7 ^ 1 := by simpa using isSLTwoOver_unique hY h7
    exact Or.inl ⟨rfl, Nat.pow_right_injective (by norm_num) hk, hA⟩
  · have hk : 5 ^ k = 5 ^ 1 := by simpa using isSLTwoOver_unique hY h5
    exact Or.inr (Or.inl ⟨rfl, Nat.pow_right_injective (by norm_num) hk, hB⟩)
  · have hk : 3 ^ k = 3 ^ 2 := by simpa using isSLTwoOver_unique hY h9
    exact Or.inr (Or.inr ⟨rfl, Nat.pow_right_injective (by norm_num) hk, hC⟩)

end CFSG.OddStandard.HigherRank
