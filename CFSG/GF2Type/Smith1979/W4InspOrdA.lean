module

public import CFSG.Timmesfeld.Orders.Distinct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp.Survivors

open CFSG.Open CFSG.Timmesfeld.Orders

theorem le_of_two_pow_dvd {m k : ℕ} (hk : 2 ^ k ∣ m)
    (hd : m ∣ 348364800 ∨ m ∣ 394813440) : k ≤ 13 := by
  by_contra hlt
  have h14 : 2 ^ 14 ∣ m := (pow_dvd_pow 2 (by omega)).trans hk
  rcases hd with h | h
  · exact absurd (h14.trans h) (by decide)
  · exact absurd (h14.trans h) (by decide)

theorem two_pow_dvd_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) : 2 ^ N ∣ m :=
  let ⟨r, _, hr⟩ := h.two
  ⟨r, hr⟩

theorem false_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hN : 14 ≤ N)
    (hd : m ∣ 348364800 ∨ m ∣ 394813440) : False := by
  have := le_of_two_pow_dvd (two_pow_dvd_of_profile h) hd
  omega

theorem psl_numeric {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hd : ordA (n - 1) (2 ^ f) ∣ 348364800 ∨ ordA (n - 1) (2 ^ f) ∣ 394813440) :
    (n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1) := by
  have hk := le_of_two_pow_dvd
    (two_pow_dvd_of_profile (profile_ordA (n := n - 1) (by omega) hf)) hd
  have hn5 : n ≤ 5 := by
    by_contra hlt
    have h30 : 5 * 6 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left ((n - 1) * (n - 1 + 1) / 2) hf
    omega
  interval_cases n
  · have hf4 : f ≤ 4 := by norm_num at hk; omega
    interval_cases f
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd hd (by decide +kernel)
    · exact absurd hd (by decide +kernel)
  · have hf2 : f ≤ 2 := by norm_num at hk; omega
    interval_cases f
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact absurd hd (by decide +kernel)
  · have hf1 : f = 1 := by norm_num at hk; omega
    subst hf1
    exact absurd hd (by decide +kernel)

theorem psp_numeric {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hd : ordBC n (2 ^ f) ∣ 348364800 ∨ ordBC n (2 ^ f) ∣ 394813440) : n = 3 ∧ f = 1 := by
  have hk := le_of_two_pow_dvd (two_pow_dvd_of_profile (profile_ordBC (n := n) hf)) hd
  have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
  have hn3 : n = 3 := by
    by_contra hne
    have h16 : 4 * 4 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * n) hf
    omega
  subst hn3
  exact ⟨rfl, by omega⟩

theorem pomegaPlus_numeric {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hd : ordD n (2 ^ f) ∣ 348364800 ∨ ordD n (2 ^ f) ∣ 394813440) : n = 4 ∧ f = 1 := by
  have hk := le_of_two_pow_dvd (two_pow_dvd_of_profile (profile_ordD (n := n) (by omega) hf)) hd
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have hn4 : n = 4 := by
    by_contra hne
    have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    omega
  subst hn4
  exact ⟨rfl, by omega⟩

theorem pomegaMinus_numeric {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hd : ordTwistedD n (2 ^ f) ∣ 348364800 ∨ ordTwistedD n (2 ^ f) ∣ 394813440) :
    n = 4 ∧ f = 1 := by
  have hk := le_of_two_pow_dvd
    (two_pow_dvd_of_profile (profile_ordTwistedD (n := n) (by omega) hf)) hd
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have hn4 : n = 4 := by
    by_contra hne
    have h20 : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    omega
  subst hn4
  exact ⟨rfl, by omega⟩

theorem g2_numeric {f : ℕ} (hf : 2 ≤ f)
    (hd : ordG2 (2 ^ f) ∣ 348364800 ∨ ordG2 (2 ^ f) ∣ 394813440) : False := by
  have hk := le_of_two_pow_dvd (two_pow_dvd_of_profile (profile_ordG2 (f := f) (by omega))) hd
  obtain rfl : f = 2 := by omega
  exact absurd hd (by decide +kernel)

theorem trialityD4_numeric {f : ℕ} (hf : 1 ≤ f)
    (hd : ordTrialityD4 (2 ^ f) ∣ 348364800 ∨ ordTrialityD4 (2 ^ f) ∣ 394813440) : False := by
  have hk := le_of_two_pow_dvd
    (two_pow_dvd_of_profile (profile_ordTrialityD4 (f := f) hf)) hd
  obtain rfl : f = 1 := by omega
  exact absurd hd (by decide +kernel)

end CFSG.GF2Type.Smith1979.W4Insp.Survivors
