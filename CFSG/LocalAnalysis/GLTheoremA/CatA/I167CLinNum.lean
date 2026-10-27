module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem i167CLin_halfSplit_cases_aux1 {p l n : ℕ}
    (hhs : GLAHalfSplit16 p ⟨.A, l, n⟩ True) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ (l = 5 ∧ n = 2 ∧ p = 5) ∨
      (l = 8 ∧ n = 1 ∧ p = 7) := by
  simp [GLAHalfSplit16, CFSG.Assembly.LargeEvenHalfSplit16, CFSG.Assembly.LargeEvenSplit16,
    CFSG.Assembly.LargeEvenUntwisted] at hhs
  rcases hhs with h | h
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

private theorem i167CLin_halfSplit_cases_aux2 {p n : ℕ}
    (hhs : GLAHalfSplit16 p ⟨.D, 3, n⟩ True) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ p ∣ 2 ^ n + 1 := by
  simp [GLAHalfSplit16, CFSG.Assembly.LargeEvenHalfSplit16, CFSG.Assembly.LargeEvenSplit16,
    CFSG.Assembly.LargeEvenUntwisted] at hhs
  rcases hhs with h | h
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem i167CLin_halfSplit_cases_aux3 {p m : ℕ}
    (hhs : GLAHalfSplit16 p ⟨.twD, 2, m⟩ True) : p ∣ 2 ^ (2 * m) - 1 := by
  have hident : (2 ^ m + 1) * (2 ^ m - 1) = 2 ^ (2 * m) - 1 := by
    rw [← Nat.sq_sub_sq, ← pow_mul]
    congr 2
    ring
  simp [GLAHalfSplit16, CFSG.Assembly.LargeEvenHalfSplit16, CFSG.Assembly.LargeEvenSplit16,
    CFSG.Assembly.LargeEvenUntwisted] at hhs
  rcases hhs with h | h
  · rw [← hident]
    exact dvd_mul_of_dvd_left h _
  · rcases h with h | h
    · rw [← hident]
      exact dvd_mul_of_dvd_right h _
    · obtain ⟨rfl, rfl⟩ := h
      norm_num

private theorem i167CLin_halfSplit_cases_aux4 {p : ℕ} {labK : GLALabel}
    (hFam : Y10GField.FamLin labK) (hhs : GLAHalfSplit16 p labK True) :
    p ∣ 2 ^ (canonLabel labK).n - 1 ∨ ((canonLabel labK).n = 1 ∧ p = 3) ∨
      ((canonLabel labK).rank = 5 ∧ (canonLabel labK).n = 2 ∧ p = 5) ∨
      ((canonLabel labK).rank = 8 ∧ (canonLabel labK).n = 1 ∧ p = 7) ∨
      ((canonLabel labK).rank = 3 ∧ p ∣ 2 ^ (canonLabel labK).n + 1) := by
  obtain ⟨kt, kr, kn⟩ := labK
  change kt = .A ∨ (kt = .D ∧ kr = 3) ∨ (kt = .twD ∧ kr = 2) at hFam
  rcases hFam with hA | ⟨hD, hr3⟩ | ⟨hD2, hr2⟩
  · subst kt
    rcases i167CLin_halfSplit_cases_aux1 hhs with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · subst kt
    subst kr
    have hc : canonLabel (⟨.D, 3, kn⟩ : GLALabel) = ⟨.A, 3, kn⟩ := rfl
    rw [hc]
    rcases i167CLin_halfSplit_cases_aux2 hhs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
  · subst kt
    subst kr
    exact Or.inl (i167CLin_halfSplit_cases_aux3 hhs)

theorem i167CLin_halfSplit_cases {p : ℕ} {labK : GLALabel} (hFam : Y10GField.FamLin labK)
    (h : HalfSplitLab p labK) :
    p ∣ 2 ^ (canonLabel labK).n - 1 ∨ ((canonLabel labK).n = 1 ∧ p = 3) ∨
      ((canonLabel labK).rank = 5 ∧ (canonLabel labK).n = 2 ∧ p = 5) ∨
      ((canonLabel labK).rank = 8 ∧ (canonLabel labK).n = 1 ∧ p = 7) ∨
      ((canonLabel labK).rank = 3 ∧ p ∣ 2 ^ (canonLabel labK).n + 1) := by
  obtain ⟨labH, hiso, hhs⟩ := h
  obtain ⟨kt, kr, kn⟩ := labK
  obtain ⟨ht, hr, hn⟩ := labH
  change kt = .A ∨ (kt = .D ∧ kr = 3) ∨ (kt = .twD ∧ kr = 2) at hFam
  unfold CFSG.StandardType.GGLabelIso at hiso
  simp only [CFSG.Assembly.LargeEvenLabel.mk.injEq] at hiso
  rcases hiso with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · obtain ⟨rfl, rfl, rfl⟩ := h1
    exact i167CLin_halfSplit_cases_aux4 hFam hhs
  · exfalso
    rcases hFam with hA | ⟨hD, -⟩ | ⟨hD2, -⟩ <;> simp_all
  · obtain ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ := h3
    rcases i167CLin_halfSplit_cases_aux2 hhs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
  · obtain ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ := h4
    rcases i167CLin_halfSplit_cases_aux1 hhs with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · simp at h
    · simp at h
  · exfalso
    obtain ⟨-, hkt, -⟩ := h5
    rw [hkt] at hFam
    simp_all
  · exfalso
    obtain ⟨-, hkt, hkr, -⟩ := h6
    rw [hkt, hkr] at hFam
    simp_all
  · obtain ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ := h7
    exact Or.inl (i167CLin_halfSplit_cases_aux3 hhs)
  · obtain ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ := h8
    rcases i167CLin_halfSplit_cases_aux1 hhs with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · simp at h
    · simp at h

theorem i167CLin_num_pdvd {p a e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ a - 1) (h2 : a ∣ e) :
    p ∣ 2 ^ e - 1 ∧ ¬ p ∣ 2 ^ e + 1 := by
  obtain ⟨t, rfl⟩ := h2
  have h3 : p ∣ 2 ^ (a * t) - 1 := by
    rw [pow_mul]
    exact h1.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 t)
  constructor
  · simpa [mul_comm] using h3
  · intro h4
    have h5 : p ∣ 2 := by
      have hle : 1 ≤ 2 ^ (a * t) := Nat.one_le_two_pow
      have heq : 2 ^ (a * t) + 1 - (2 ^ (a * t) - 1) = 2 := by omega
      have h := Nat.dvd_sub h4 h3
      rwa [heq] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
