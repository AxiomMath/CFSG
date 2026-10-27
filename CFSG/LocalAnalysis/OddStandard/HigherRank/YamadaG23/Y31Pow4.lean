module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem srel_a1h0_pow4 {fr : SFrame Γ} (h : SRel fr) : (fr.a₁ * fr.h₀) ^ 4 = fr.z := by
  have hz2 : fr.z ^ 2 = 1 := h.z_sq
  have hh2 : fr.h₀ ^ 2 = 1 := h.h0_sq
  have ha2 : fr.a₁ ^ 2 = fr.z := h.a1_sq
  have hb2 : fr.b₁ ^ 2 = fr.z := rfl
  have hc1 : fr.a₁ * fr.b₁ * fr.a₁⁻¹ * fr.b₁⁻¹ = fr.z := h.comm1
  have hch : fr.a₁ * fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹ = fr.b₁ * fr.z := h.a1h
  have hzinv : fr.z⁻¹ = fr.z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hz2)
  have hhinv : fr.h₀⁻¹ = fr.h₀ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hh2)
  have hbinv : fr.b₁⁻¹ = fr.b₁ * fr.z :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_two, hb2, ← pow_two, hz2])
  have hcomm : fr.z * fr.b₁ = fr.b₁ * fr.z := by
    show fr.b₁ ^ 2 * fr.b₁ = fr.b₁ * fr.b₁ ^ 2
    group
  have hbz : (fr.b₁ * fr.z)⁻¹ = fr.b₁ := by
    calc (fr.b₁ * fr.z)⁻¹ = fr.z⁻¹ * fr.b₁⁻¹ := mul_inv_rev _ _
      _ = fr.z * (fr.b₁ * fr.z) := by rw [hzinv, hbinv]
      _ = fr.b₁ := by rw [← mul_assoc, hcomm, mul_assoc, ← pow_two, hz2, mul_one]
  have hinv : fr.h₀ * fr.a₁ * fr.h₀⁻¹ * fr.a₁⁻¹ = (fr.b₁ * fr.z)⁻¹ := by
    calc fr.h₀ * fr.a₁ * fr.h₀⁻¹ * fr.a₁⁻¹
        = (fr.a₁ * fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹)⁻¹ := by group
      _ = (fr.b₁ * fr.z)⁻¹ := by rw [hch]
  have hhah : fr.h₀ * fr.a₁ * fr.h₀⁻¹ = (fr.b₁ * fr.z)⁻¹ * fr.a₁ := by
    calc fr.h₀ * fr.a₁ * fr.h₀⁻¹
        = (fr.h₀ * fr.a₁ * fr.h₀⁻¹ * fr.a₁⁻¹) * fr.a₁ := by group
      _ = (fr.b₁ * fr.z)⁻¹ * fr.a₁ := by rw [hinv]
  have hha : fr.h₀ * fr.a₁ * fr.h₀ = fr.b₁ * fr.a₁ := by
    rw [hhinv] at hhah
    rw [hhah, hbz]
  have hab : fr.a₁ * fr.b₁ = fr.z * fr.b₁ * fr.a₁ := by
    calc fr.a₁ * fr.b₁
        = (fr.a₁ * fr.b₁ * fr.a₁⁻¹ * fr.b₁⁻¹) * (fr.b₁ * fr.a₁) := by group
      _ = fr.z * (fr.b₁ * fr.a₁) := by rw [hc1]
      _ = fr.z * fr.b₁ * fr.a₁ := by group
  have haba : fr.a₁ * fr.b₁ * fr.a₁ = fr.b₁ := by
    calc fr.a₁ * fr.b₁ * fr.a₁ = (fr.z * fr.b₁ * fr.a₁) * fr.a₁ := by rw [hab]
      _ = fr.z * fr.b₁ * (fr.a₁ * fr.a₁) := by group
      _ = fr.z * fr.b₁ * fr.z := by rw [← pow_two, ha2]
      _ = fr.b₁ := by rw [hcomm, mul_assoc, ← pow_two, hz2, mul_one]
  have hsq : (fr.a₁ * fr.h₀) ^ 2 = fr.b₁ := by
    calc (fr.a₁ * fr.h₀) ^ 2 = fr.a₁ * (fr.h₀ * fr.a₁ * fr.h₀) := by rw [pow_two]; group
      _ = fr.a₁ * (fr.b₁ * fr.a₁) := by rw [hha]
      _ = fr.b₁ := by rw [← mul_assoc]; exact haba
  have h4 : (fr.a₁ * fr.h₀) ^ 4 = fr.b₁ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  exact h4

end CFSG.OddStandard.HigherRank.YamadaG23
