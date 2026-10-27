module

public import CFSG.GH74.GLS.Stage4.HexWeights
public import CFSG.GH74.GLS.Stage4.HexCSL2

public section

namespace CFSG.GH74.GLS.Stage4.Rest.ZF

open CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {F : Type} [Field F]

theorem sl2_kit_identity (h2 : (2 : F) ≠ 0) :
    sl2L (-1 : F) * sl2U (2⁻¹ : F) = sl2W F * (sl2L (1 : F) * sl2U (-(2⁻¹ : F))) := by
  apply sl2_ext
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h22
  · linear_combination -h22

theorem sl2_kit_identity_w :
    sl2U (-1 : F) * sl2L (1 : F) * sl2U (-1 : F) = sl2D (-1 : Fˣ) * sl2W F := by
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_eq_ULU : sl2W F = sl2U (1 : F) * sl2L (-1 : F) * sl2U (1 : F) := by
  rw [sl2W_eq_sl2Wc]
  simp [sl2Wc]


theorem sl2_u_kit (h2 : (2 : F) ≠ 0) (φ : SL2 F →* G) (hφ : Function.Injective φ) {Hs : Subgroup G}
    (hcomm : ∀ a ∈ Hs, ∀ b ∈ Hs, a * b = b * a) (hD : ∀ t : Fˣ, φ (sl2D t) ∈ Hs) {u : G}
    (hu : u ∈ Hs) (huu : u * u = 1) (hU : ∀ c, ∃ d, u * φ (sl2U c) * u⁻¹ = φ (sl2U d))
    (hL : ∀ c, ∃ d, u * φ (sl2L c) * u⁻¹ = φ (sl2L d))
    (hnc : u * φ (sl2U 1) * u⁻¹ ≠ φ (sl2U 1)) :
    u * φ (sl2L 1 * sl2U (-(2⁻¹ : F))) * u⁻¹ = φ (sl2W F) * φ (sl2L 1 * sl2U (-(2⁻¹ : F))) ∧
      u * φ (sl2W F) * u⁻¹ = φ (sl2D (-1 : Fˣ)) * φ (sl2W F) := by
  obtain ⟨a, ha, hAU, hBL⟩ := exists_scalar_of_normalizes h2 φ hφ hcomm hD hu hU hL
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have haa : a * a = 1 := by
    have h1 : u * (u * φ (sl2U 1) * u⁻¹) * u⁻¹ = φ (sl2U 1) := by
      rw [hui]
      calc u * (u * φ (sl2U 1) * u) * u = (u * u) * φ (sl2U 1) * (u * u) := by group
        _ = φ (sl2U 1) := by rw [huu]; group
    rw [hAU 1, hAU (a * 1)] at h1
    have h3 := sl2U_injective (hφ h1)
    simpa [mul_assoc] using h3
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hnc (by rw [hAU 1, mul_one])
  have ham : a = -1 := by
    rcases mul_self_eq_one_iff.1 haa with h | h
    · exact absurd h ha1
    · exact h
  subst ham
  have hinv : ((-1 : F))⁻¹ = -1 := by simp
  refine ⟨?_, ?_⟩
  · have e1 : u * φ (sl2L 1 * sl2U (-(2⁻¹ : F))) * u⁻¹ =
        (u * φ (sl2L 1) * u⁻¹) * (u * φ (sl2U (-(2⁻¹ : F))) * u⁻¹) := by
      rw [map_mul]; group
    rw [e1, hBL, hAU, ← map_mul, ← map_mul, hinv, neg_one_mul, neg_one_mul, neg_neg,
      sl2_kit_identity h2]
  · have e1 : u * φ (sl2W F) * u⁻¹ =
        (u * φ (sl2U (1 : F)) * u⁻¹) * (u * φ (sl2L (-1 : F)) * u⁻¹) * (u * φ (sl2U (1 : F)) * u⁻¹) := by
      rw [sl2W_eq_ULU, map_mul, map_mul]; group
    rw [e1, hBL, hAU, ← map_mul, ← map_mul, hinv, neg_one_mul, neg_one_mul, neg_neg,
      sl2_kit_identity_w, map_mul]

end CFSG.GH74.GLS.Stage4.Rest.ZF
