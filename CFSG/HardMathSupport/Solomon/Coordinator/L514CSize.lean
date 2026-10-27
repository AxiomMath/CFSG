module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514CIso

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem l514c_bounds_of_formula {r N g c : ℕ} (hr : 2 ≤ r) (hg1 : 1 ≤ g) (hg3 : g ≤ 3)
    (hc : c = 1 ∨ c = 0)
    (h : N * g = r ^ 3 * ((r ^ 2 - 1) * (if c = 1 then r ^ 3 + 1 else r ^ 3 - 1))) :
    N ≤ 2 * r ^ 8 ∧ r ^ 8 ≤ 12 * N := by
  obtain ⟨s, hs⟩ : ∃ s, r ^ 2 = s + 1 := ⟨r ^ 2 - 1, by have : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  obtain ⟨t, ht⟩ : ∃ t, r ^ 3 = t + 1 := ⟨r ^ 3 - 1, by have : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hs2 : 2 ≤ s := by nlinarith
  have ht2 : 2 ≤ t := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℕ) ≤ 2) hr 3]
  have h8 : r ^ 8 = (s + 1) * (t + 1) * (t + 1) := by
    rw [← hs, ← ht]; ring
  have hs' : r ^ 2 - 1 = s := by omega
  have ht' : r ^ 3 - 1 = t := by omega
  have hNg1 : N ≤ N * g := Nat.le_mul_of_pos_right N hg1
  have hNg3 : N * g ≤ N * 3 := Nat.mul_le_mul_left N hg3
  rcases hc with rfl | rfl
  · simp only [ite_true, hs'] at h
    rw [ht] at h
    have hu : (t + 1) * (s * (t + 1 + 1)) ≤ 2 * ((s + 1) * (t + 1) * (t + 1)) := by
      calc (t + 1) * (s * (t + 1 + 1)) ≤ (t + 1) * ((s + 1) * (2 * (t + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ = 2 * ((s + 1) * (t + 1) * (t + 1)) := by ring
    have hl : (s + 1) * (t + 1) * (t + 1) ≤ 2 * ((t + 1) * (s * (t + 1 + 1))) := by
      calc (s + 1) * (t + 1) * (t + 1) ≤ (2 * s) * (t + 1) * (t + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
        _ ≤ 2 * ((t + 1) * (s * (t + 1 + 1))) := by nlinarith
    constructor
    · rw [h8]; omega
    · rw [h8]; omega
  · simp only [show (0 : ℕ) ≠ 1 by norm_num, ite_false, hs', ht'] at h
    rw [ht] at h
    have hu : (t + 1) * (s * t) ≤ 2 * ((s + 1) * (t + 1) * (t + 1)) := by
      nlinarith
    have hl : (s + 1) * (t + 1) * (t + 1) ≤ 4 * ((t + 1) * (s * t)) := by
      calc (s + 1) * (t + 1) * (t + 1) ≤ (2 * s) * (2 * t) * (t + 1) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (le_refl _)
        _ = 4 * ((t + 1) * (s * t)) := by ring
    constructor
    · rw [h8]; omega
    · rw [h8]; omega

theorem l514c_card_bounds {r : ℕ} {Y : Type} [Group Y] (h : IsL3Raw r Y) :
    2 ≤ r ∧ Nat.card Y ≤ 2 * r ^ 8 ∧ r ^ 8 ≤ 12 * Nat.card Y := by
  rcases h with h | h
  · obtain ⟨p, a, hp, ha, rfl, h1⟩ := l514c_card_psl h
    have hr : 2 ≤ p ^ a := by
      have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
      omega
    have := l514c_bounds_of_formula (c := 0) hr
      (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
      (Or.inr rfl) (by simpa using h1)
    exact ⟨hr, this⟩
  · obtain ⟨p, a, hp, ha, rfl, h1⟩ := l514c_card_psu h
    have hr : 2 ≤ p ^ a := by
      have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
      omega
    have := l514c_bounds_of_formula (c := 1) hr
      (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_le_left _ (by norm_num))
      (Or.inl rfl) (by simpa using h1)
    exact ⟨hr, this⟩

theorem lemma514Cover_inputL3size_holds : LocalBalance.Lemma514CoverNs.InputL3size := by
  intro Y Y' _ _ _ _ r h h'
  obtain ⟨hr, h1, -⟩ := l514c_card_bounds h
  obtain ⟨hr', -, h2⟩ := l514c_card_bounds h'
  have h3 : (r ^ 3) ^ 8 = r ^ 8 * r ^ 16 := by ring
  have h4 : 2 ^ 16 ≤ r ^ 16 := Nat.pow_le_pow_left hr 16
  have h5 : r ^ 8 * 2 ^ 16 ≤ r ^ 8 * r ^ 16 := Nat.mul_le_mul_left _ h4
  have h6 : 0 < r ^ 8 := by positivity
  rw [h3] at h2
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
