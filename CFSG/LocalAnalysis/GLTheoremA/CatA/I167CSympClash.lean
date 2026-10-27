module

public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem i167CS_clash_aux1 {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ k - 1)
    (h2 : p ∣ 2 ^ k + 1) : False := by
  have h3 := Nat.dvd_sub h2 h1
  have h4 : 2 ^ k + 1 - (2 ^ k - 1) = 2 := by
    have := Nat.one_le_two_pow (n := k)
    omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

private theorem i167CS_clash_aux2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : GLALabel}
    {N k : ℕ} (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1)
    (hc : canonLabel lab = if N = 3 then ⟨.A, 3, k⟩ else ⟨.D, N, k⟩)
    (hM : (∃ a k' : ℕ, 2 ≤ a ∧ (a = 2 ∨ p ∣ 2 ^ k' - 1) ∧ canonLabel lab = ⟨.A, a - 1, k'⟩) ∨
      (∃ a k' : ℕ, canonLabel lab = ⟨.twA, a - 1, k'⟩ ∨ canonLabel lab = ⟨.A, 1, k'⟩) ∨
      (∃ s n : ℕ, canonLabel lab = ⟨.B, s, n⟩)) : False := by
  by_cases h3 : N = 3
  · rw [if_pos h3] at hc
    rcases hM with ⟨a, k', ha, hd, h⟩ | ⟨a, k', h | h⟩ | ⟨s, n, h⟩
    · rw [hc] at h
      simp at h
      obtain ⟨h1, rfl⟩ := h
      rcases hd with h2 | hd
      · omega
      · exact i167CS_clash_aux1 hp hp2 hd hpk
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
  · rw [if_neg h3] at hc
    rcases hM with ⟨a, k', ha, hd, h⟩ | ⟨a, k', h | h⟩ | ⟨s, n, h⟩ <;>
    · rw [hc] at h
      simp at h

theorem i167CS_clash {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : GLALabel}
    (hT : (p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
      (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
      (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
        canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩))
    (hM : (∃ a k : ℕ, 2 ≤ a ∧ (a = 2 ∨ p ∣ 2 ^ k - 1) ∧ canonLabel lab = ⟨.A, a - 1, k⟩) ∨
      (∃ a k : ℕ, canonLabel lab = ⟨.twA, a - 1, k⟩ ∨ canonLabel lab = ⟨.A, 1, k⟩) ∨
      (∃ s n : ℕ, canonLabel lab = ⟨.B, s, n⟩)) : False := by
  rcases hT with ⟨-, N, hN, hc⟩ | ⟨-, N, hN, hc⟩ | ⟨N, k, hN, hk, hpk, hc⟩
  · rcases hM with ⟨a, k, ha, hd, h⟩ | ⟨a, k, h | h⟩ | ⟨s, n, h⟩
    · rw [hc] at h
      simp at h
      obtain ⟨h1, rfl⟩ := h
      rcases hd with h2 | hd
      · omega
      · rw [pow_one] at hd
        simp at hd
        exact hp.ne_one hd
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
      omega
    · rw [hc] at h
      simp at h
  · rcases hM with ⟨a, k, ha, hd, h⟩ | ⟨a, k, h | h⟩ | ⟨s, n, h⟩ <;>
    · rw [hc] at h
      simp at h
  · exact i167CS_clash_aux2 hp hp2 hk hpk hc hM

end CFSG.LocalAnalysis.GLTheoremA.I167

end
