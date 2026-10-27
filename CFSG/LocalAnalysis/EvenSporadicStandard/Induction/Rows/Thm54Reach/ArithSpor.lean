module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Arith

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.ComponentClassification.GSThmB.QPUSpor

theorem Thm54Order.ne_sporOrder {c : ℕ} (hc : Thm54Order c) (s : TauCeti.SporadicName) :
    c ≠ sporOrder s := by
  have h47 : ∀ t : TauCeti.SporadicName, ¬ 2 ^ 47 ∣ sporOrder t := by
    intro t
    cases t <;> simp only [sporOrder, sporFactors] <;> decide
  intro h
  rcases hc with ⟨f, hf, hodd, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have h2 : 2 ^ (2 * f) ∣ sporOrder s := by rw [← h]; exact dvd_mul_right _ _
    have hle : 2 * f ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 2 * f)).trans h2)
    have hf23 : f ≤ 23 := by omega
    interval_cases f <;>
      (first | exact absurd hodd (by decide) | (revert s; decide))
  · have h2 : 2 ^ (4 * m) ∣ sporOrder s := by rw [← h]; exact dvd_mul_right _ _
    have hle : 4 * m ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 4 * m)).trans h2)
    have hm11 : m ≤ 11 := by omega
    interval_cases m <;> (revert s; decide)
  · have h2 : 2 ^ (6 * m) ∣ sporOrder s := by rw [← h]; exact dvd_mul_right _ _
    have hle : 6 * m ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 6 * m)).trans h2)
    have hm7 : m ≤ 7 := by omega
    interval_cases m <;> (revert s; decide)
  · have h2 : 2 ^ (6 * m) ∣ sporOrder s := by rw [← h]; exact dvd_mul_right _ _
    have hle : 6 * m ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 6 * m)).trans h2)
    have hm7 : m ≤ 7 := by omega
    interval_cases m <;> (revert s; decide)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := by
      rcases hd with rfl | rfl
      · exact Nat.coprime_one_right _
      · exact Nat.Coprime.pow_left _ (by decide)
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2s : 2 ^ (10 * m) ∣ sporOrder s := by rw [← h]; exact h2
    have hle : 10 * m ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 10 * m)).trans h2s)
    have hm4 : m ≤ 4 := by omega
    rcases hd with rfl | rfl
    · have hce : c = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by simpa using hcd
      rw [hce] at h
      interval_cases m <;> (revert s; decide)
    · have hce : c = (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) / 5 :=
        Nat.eq_div_of_mul_eq_left (by norm_num) hcd
      rw [hce] at h
      interval_cases m <;> (revert s; decide)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := by
      rcases hd with rfl | rfl
      · exact Nat.coprime_one_right _
      · exact Nat.Coprime.pow_left _ (by decide)
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2s : 2 ^ (10 * m) ∣ sporOrder s := by rw [← h]; exact h2
    have hle : 10 * m ≤ 46 := by
      by_contra hc'
      exact h47 s ((Nat.pow_dvd_pow 2 (by omega : 47 ≤ 10 * m)).trans h2s)
    have hm4 : m ≤ 4 := by omega
    rcases hd with rfl | rfl
    · have hce : c = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by simpa using hcd
      rw [hce] at h
      interval_cases m <;> (revert s; decide)
    · have hce : c = (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))))) / 5 :=
        Nat.eq_div_of_mul_eq_left (by norm_num) hcd
      rw [hce] at h
      interval_cases m <;> (revert s; decide)

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
