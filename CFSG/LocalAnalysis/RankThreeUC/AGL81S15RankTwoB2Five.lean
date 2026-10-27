module

public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin.B42Sp4 (fixK card_fixK eq_bot_of_finrank_fixK card_le_of_finrank_fixK_three)

theorem card_mul_card_fixK_le_pow_five {K : Type} [Field K] [Finite K] [CharP K 2]
    (Γ₀ : Subgroup (StatedSp 2 K)) (hΓ : ∀ x ∈ Γ₀, x * x = 1) :
    Nat.card Γ₀ * Nat.card ↥(fixK Γ₀) ≤ Nat.card K ^ 5 := by
  set q := Nat.card K with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  set c := Module.finrank K (fixK Γ₀) with hc
  have hc4 : c ≤ 4 := by
    have := Submodule.finrank_le (fixK Γ₀)
    rw [Module.finrank_fintype_fun_eq_card] at this
    simpa using this
  rw [card_fixK]
  have hcube := CFSG.Quasithin.H.Sp4.card_le_cube Γ₀ hΓ
  rcases (by omega : c = 4 ∨ c = 3 ∨ c ≤ 2) with h4 | h3 | h2
  · have hb := eq_bot_of_finrank_fixK (Γ₀ := Γ₀) (by omega)
    have h1 : Nat.card Γ₀ = 1 := by rw [hb, Subgroup.card_bot]
    rw [h1, ← hc, h4, one_mul]
    exact Nat.pow_le_pow_right hq1 (by norm_num)
  · have h1 := card_le_of_finrank_fixK_three (Γ₀ := Γ₀) (by omega)
    rw [← hc, h3]
    calc Nat.card Γ₀ * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ h1
      _ ≤ q ^ 5 := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right hq1 (by norm_num)
  · rw [← hc]
    calc Nat.card Γ₀ * q ^ c ≤ q ^ 3 * q ^ 2 :=
          Nat.mul_le_mul hcube (Nat.pow_le_pow_right hq1 h2)
      _ = q ^ 5 := by ring

end CFSG.LocalAnalysis.RankThreeUC.S15

end
