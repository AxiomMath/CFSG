module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CUniNum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i167CU_clash {p n0 : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : GLALabel}
    (hnum : p ∣ 2 ^ (2 * n0) - 1) (hn0 : 1 ≤ n0)
    (hT : (p = 3 ∧ ∃ n : ℕ, 5 ≤ n ∧ canonLabel lab = ⟨.A, n - 1, 1⟩) ∨
      (p = 3 ∧ ∃ n : ℕ, 6 ≤ n ∧ canonLabel lab = ⟨.twD, n, 1⟩) ∨
      (∃ n k : ℕ, 3 ≤ n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
        canonLabel lab = if n = 3 then ⟨.A, 3, k⟩ else ⟨.D, n, k⟩))
    (hM : (∃ a m : ℕ, n0 ∣ m ∧
        (canonLabel lab = ⟨.twA, a - 1, m⟩ ∨ canonLabel lab = ⟨.A, 1, m⟩)) ∨
      (∃ b e : ℕ, 1 ≤ e ∧ canonLabel lab = ⟨.A, b - 1, n0 * (2 * e)⟩)) : False := by
  rcases hT with ⟨-, n, hn, hc⟩ | ⟨-, n, hn, hc⟩ | ⟨n, k, hn, hk, hpk, hc⟩
  · rcases hM with ⟨a, m, -, h | h⟩ | ⟨b, e, he, h⟩
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
      omega
    · rw [hc] at h
      simp at h
      have : 2 ≤ n0 * (2 * e) := by nlinarith
      omega
  · rcases hM with ⟨a, m, -, h | h⟩ | ⟨b, e, he, h⟩
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
    · rw [hc] at h
      simp at h
  · by_cases h3 : n = 3
    · rw [if_pos h3] at hc
      rcases hM with ⟨a, m, -, h | h⟩ | ⟨b, e, he, h⟩
      · rw [hc] at h
        simp at h
      · rw [hc] at h
        simp at h
      · have hkeq : k = n0 * (2 * e) := congrArg (fun l : GLALabel => l.n) (hc.symm.trans h)
        subst hkeq
        exact i167CU_not_dvd_pow_add_one hp hp2 hnum ⟨e, by ring⟩ hpk
    · rw [if_neg h3] at hc
      rcases hM with ⟨a, m, -, h | h⟩ | ⟨b, e, he, h⟩
      · rw [hc] at h
        simp at h
      · rw [hc] at h
        simp at h
      · rw [hc] at h
        simp at h

end CFSG.LocalAnalysis.GLTheoremA.I167

end
