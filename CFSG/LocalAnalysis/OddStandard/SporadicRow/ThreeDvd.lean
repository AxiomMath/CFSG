module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.ThreeDvdClassical
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.ThreeDvdExceptional

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Assembly.LowTwoRank CatLeaf

theorem OddLieOrder.three_dvd {m : ℕ} (h : OddLieOrder m) : 3 ∣ m := by
  obtain ⟨τ, n, p, f, hp, hp2, ha, hnum, hfac⟩ := h
  by_cases hp3 : p = 3
  ·
    subst hp3
    obtain ⟨hN1, -⟩ := lieSylowExponent_bounds ha
    have hf1 : 1 ≤ f := ha.2.1
    have hNf : 1 ≤ lieSylowExponent τ n * f := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact Nat.dvd_of_factorization_pos (by rw [hfac]; omega)
  have hq : ¬ 3 ∣ p ^ f := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  cases τ
  · exact three_dvd_of_classical ha (Or.inl rfl) hq hnum
  · exact three_dvd_of_classical ha (Or.inr (Or.inl rfl)) hq hnum
  · exact three_dvd_of_classical ha (Or.inr (Or.inr (Or.inl rfl))) hq hnum
  · exact three_dvd_of_classical ha (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hq hnum
  · exact three_dvd_of_classical ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hq hnum
  · exact three_dvd_of_classical ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inl rfl) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inl rfl)) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inr (Or.inl rfl))) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hq hnum
  · exact three_dvd_of_exceptional ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hq hnum
  ·
    obtain ⟨-, hp', -⟩ := ha.2.2
    exact absurd hp' hp2
  ·
    obtain ⟨-, hp', -⟩ := ha.2.2
    exact absurd hp' hp3
  ·
    obtain ⟨-, hp', -⟩ := ha.2.2
    exact absurd hp' hp2
  ·
    obtain ⟨-, hp', -⟩ := ha.2.2
    exact absurd hp' hp2

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
