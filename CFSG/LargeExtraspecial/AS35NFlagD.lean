module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.AS35KRbar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35N

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LargeExtraspecial.AS35K
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem omega_sq_add : ω * ω + ω + 1 = 0 := by
  have h1 := frob_omega
  rw [frob_apply, sq] at h1
  rw [h1, add_assoc, add_self_K]

theorem K_cases' (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω + 1 := by
  have : Finite K := AS35U.hF.finite
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, card_K]
    norm_num
  have h4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rwa [hcard] at this
  have h2 : (2 : K) = 0 := two_eq_zero
  have hprod : c * (c + 1) * (c + ω) * (c + (ω + 1)) = 0 := by
    linear_combination h4 + ((ω + 1) * c ^ 3 + ω * c ^ 2) * h2 + (c ^ 2 + c) * omega_sq_add
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by rw [← neg_K 1]; exact eq_neg_of_add_eq_zero_left h))
    · exact Or.inr (Or.inr (Or.inl (by rw [← neg_K ω]; exact eq_neg_of_add_eq_zero_left h)))
  · exact Or.inr (Or.inr (Or.inr (by rw [← neg_K (ω + 1)]; exact eq_neg_of_add_eq_zero_left h)))

theorem ringEquiv_cases (φ : K ≃+* K) : (∀ c, φ c = c) ∨ φ ω = frob ω := by
  have hφ2 : φ ω * φ ω + φ ω + 1 = 0 := by
    rw [← map_mul, ← map_add, ← map_one φ, ← map_add, omega_sq_add, map_zero]
  have hcases : φ ω = ω ∨ φ ω = ω + 1 := by
    rcases K_cases' (φ ω) with h | h | h | h
    · exfalso
      rw [h] at hφ2
      simp at hφ2
    · exfalso
      rw [h, one_mul, add_self_K, zero_add] at hφ2
      exact one_ne_zero hφ2
    · exact Or.inl h
    · exact Or.inr h
  rcases hcases with h | h
  · left
    intro c
    rcases K_cases' c with rfl | rfl | rfl | rfl
    · exact map_zero φ
    · exact map_one φ
    · exact h
    · rw [map_add, map_one, h]
  · right
    rw [h, frob_omega]

end CFSG.LargeExtraspecial.AS35N
