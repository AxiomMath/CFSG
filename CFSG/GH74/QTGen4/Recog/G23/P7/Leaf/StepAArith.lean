module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem leafStepAArith
    : LeafStepAArith := by
  intro g x₁ x₂ h hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨-, n27, -, -, -, s36m⟩ := hs
  obtain rfl : x₂ = -1 - x₁ := by omega
  have hmod : x₁ % 576 = 152 := by
    unfold Int.ModEq at h2
    omega
  have hg1 : x₁ ∣ (g : ℤ) := Int.natAbs_dvd.mp (Int.ofNat_dvd_left.mpr h3)
  have hg2 : (-1 - x₁) ∣ (g : ℤ) := Int.natAbs_dvd.mp (Int.ofNat_dvd_left.mpr h4)
  obtain ⟨k, hk⟩ := (show IsCoprime x₁ (-1 - x₁) from ⟨-1, -1, by ring⟩).mul_dvd hg1 hg2
  have hP : x₁ * (-1 - x₁) ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hkey : k * (x₁ - 8) ^ 2 = -4147200 := by
    have hz : x₁ * (-1 - x₁) * (k * (x₁ - 8) ^ 2 + 4147200) = 0 := by
      rw [hk] at h5
      linear_combination (-1 : ℤ) * h5
    have := (mul_eq_zero.mp hz).resolve_left hP
    linarith
  obtain ⟨t, ht⟩ : ∃ t, x₁ - 8 = 144 * t := ⟨(x₁ - 8) / 144, by omega⟩
  have ht4 : t % 4 = 1 := by omega
  have hkt : k * (t * t) = -200 := by
    have hz : 20736 * (k * (t * t) + 200) = 0 := by
      rw [ht] at hkey
      linear_combination hkey
    have := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linarith
  have hk_neg : k < 0 := by nlinarith [mul_self_nonneg t]
  have ht2 : t * t ≤ 200 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -k - 1 by omega) (mul_self_nonneg t)]
  have ht_lo : -14 ≤ t := by nlinarith
  have ht_hi : t ≤ 14 := by nlinarith
  have ht15 : t = 1 ∨ t = 5 := by
    interval_cases t <;> omega
  rcases ht15 with rfl | rfl
  ·
    have hk' : k = -200 := by omega
    have hx : x₁ = 152 := by omega
    subst hk' hx
    have hg : (g : ℤ) = 4651200 := by norm_num [hk]
    omega
  ·
    have hk' : k = -8 := by omega
    have hx : x₁ = 728 := by omega
    subst hk' hx
    have hg : (g : ℤ) = 4245696 := by norm_num [hk]
    omega

end CFSG.GH74.QTGen4.Recog.G23.P7
