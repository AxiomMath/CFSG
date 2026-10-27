module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec89c
import CFSG.Goldschmidt.Steps.Sec89e
import CFSG.Goldschmidt.Steps.Sec89h

public section

namespace CFSG.Goldschmidt

theorem G89_of (h87 : S_G87) (h88 : S_G88) : S_G89 := by
  intro G _ _ S A hset h4 hS
  obtain ⟨hrank, hDc, -, hΩZ, hΩD⟩ := h87 G S A hset h4 hS
  have hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G),
      z * t = t * z → z ^ 2 ∈ A → z ^ 2 = 1 := by
    intro t ht ht2 htA z hz hzt hz2
    obtain ⟨B, hB, hAB, hsup⟩ := h88 G S A hset h4 hS t ht ht2 htA
    exact Sec89.sq_eq_one_of_sup_eq hset h4 hB hAB hsup
      (Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩) hz2
  have hZ := Sec89.center_le hset h4 hL hΩZ
  by_cases hD : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A
  · exact Sec89.false_of_commutator_le hset h4 hrank.le hL hZ hD
  · exact Sec89.false_of_not_commutator_le hset h4 hrank.le hL hDc hΩD hD

end CFSG.Goldschmidt
