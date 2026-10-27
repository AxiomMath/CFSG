module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni)

private theorem i167CU_split_aux1 {p n r : ℕ} {t : CFSG.Assembly.LargeEvenLieTag}
    (h : t = .twA ∨ t = .twD) (hH : CFSG.Assembly.LargeEvenHalfSplit16 p ⟨t, r, n⟩ True) :
    p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with rfl | rfl <;>
  simp [CFSG.Assembly.LargeEvenHalfSplit16, CFSG.Assembly.LargeEvenSplit16,
    CFSG.Assembly.LargeEvenUntwisted] at hH
  · rcases hH with (h | h) | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rcases hH with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem i167CU_dvd_two_mul_of_cases {p n : ℕ}
    (h : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) : p ∣ 2 ^ (2 * n) - 1 := by
  have h2n : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [mul_comm, pow_mul]
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  rcases h with h | h | ⟨rfl, rfl⟩
  · rw [h2n]; exact Dvd.dvd.mul_right h _
  · rw [h2n]; exact Dvd.dvd.mul_left h _
  · norm_num

theorem i167CU_halfSplit_dvd {p : ℕ} {labK : GLALabel} (hFam : FamUni labK) (hH : HalfSplitLab p labK) :
    p ∣ 2 ^ (2 * labK.n) - 1 := by
  obtain ⟨labH, hiso, hHS⟩ := hH
  obtain ⟨tK, rK, nK⟩ := labK
  obtain ⟨tH, rH, nH⟩ := labH
  have key : (tH = .twA ∨ tH = .twD) ∧ nH = nK := by
    unfold FamUni at hFam
    unfold CFSG.StandardType.GGLabelIso at hiso
    rcases hFam with rfl | ⟨rfl, rfl⟩ <;> simp at hiso <;> grind
  obtain ⟨ht, rfl⟩ := key
  exact i167CU_dvd_two_mul_of_cases (i167CU_split_aux1 ht hHS)

theorem i167CU_not_dvd_pow_add_one {p n m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2 ^ (2 * n) - 1)
    (hm : 2 * n ∣ m) : ¬ p ∣ 2 ^ m + 1 := by
  intro h
  have h1 : p ∣ 2 ^ m - 1 := hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hm)
  have h2 : p ∣ 2 := by
    have h3 := Nat.dvd_sub h h1
    have h4 : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by
      have := Nat.one_le_two_pow (n := m)
      omega
    rwa [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
