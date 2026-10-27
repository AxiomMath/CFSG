module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

public section

namespace CFSG.EvenSporadicStandard.Solomon78

@[expose] def hnfS : Fin 9 → ℕ :=
  ![1, 1408, 2200, 5775, 35200, 123200, 277200, 354816, 739200]

@[expose] def hnfValid (a : Fin 9 → ℕ) : Prop :=
  ∀ i, a i = 0 ∨ a i + a i = hnfS i ∨ a i = hnfS i

theorem hnfS_sum : ∑ i, hnfS i = 1539000 := by
  decide

private theorem hnf_sum_nine (a : Fin 9 → ℕ) :
    ∑ i, a i = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 := by
  simp [Fin.sum_univ_succ]
  omega

private theorem hnf_mem_even {x s h : ℕ} (hs : h + h = s) (hx : x = 0 ∨ x + x = s ∨ x = s) :
    x ∈ ([0, h, s] : List ℕ) := by
  simp
  omega

private theorem hnf_mem_odd {x s : ℕ} (hs : s % 2 = 1) (hx : x = 0 ∨ x + x = s ∨ x = s) :
    x ∈ ([0, s] : List ℕ) := by
  simp
  omega

private theorem hnf_valid_mem {a : Fin 9 → ℕ} (hv : hnfValid a) :
    a 1 ∈ ([0, 704, 1408] : List ℕ) ∧ a 2 ∈ ([0, 1100, 2200] : List ℕ) ∧
      a 3 ∈ ([0, 5775] : List ℕ) ∧ a 4 ∈ ([0, 17600, 35200] : List ℕ) ∧
      a 5 ∈ ([0, 61600, 123200] : List ℕ) ∧ a 6 ∈ ([0, 138600, 277200] : List ℕ) ∧
      a 7 ∈ ([0, 177408, 354816] : List ℕ) ∧ a 8 ∈ ([0, 369600, 739200] : List ℕ) :=
  ⟨hnf_mem_even (by decide) (hv 1), hnf_mem_even (by decide) (hv 2),
    hnf_mem_odd (by decide) (hv 3), hnf_mem_even (by decide) (hv 4),
    hnf_mem_even (by decide) (hv 5), hnf_mem_even (by decide) (hv 6),
    hnf_mem_even (by decide) (hv 7), hnf_mem_even (by decide) (hv 8)⟩

set_option synthInstance.maxSize 5000 in
set_option maxRecDepth 100000 in
private theorem hnf_main_digits :
    ∀ x1 ∈ ([0, 704, 1408] : List ℕ), ∀ x2 ∈ ([0, 1100, 2200] : List ℕ),
    ∀ x3 ∈ ([0, 5775] : List ℕ), ∀ x4 ∈ ([0, 17600, 35200] : List ℕ),
    ∀ x5 ∈ ([0, 61600, 123200] : List ℕ), ∀ x6 ∈ ([0, 138600, 277200] : List ℕ),
    ∀ x7 ∈ ([0, 177408, 354816] : List ℕ), ∀ x8 ∈ ([0, 369600, 739200] : List ℕ),
    ∀ cu ∈ ([88704000, 177408000] : List ℕ),
      (1 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) * cu ∣ 273030912000000 →
      (x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0) ∨
      (x1 = 1408 ∧ x2 = 2200 ∧ x3 = 5775 ∧ x4 = 35200 ∧ x5 = 123200 ∧ x6 = 277200 ∧
        x7 = 354816 ∧ x8 = 739200) ∨
      (cu = 88704000 ∧ x1 = 704 ∧ x2 = 0 ∧ x3 = 5775 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧
        x8 = 0) := by
  decide

theorem hnf_arith_main (a : Fin 9 → ℕ) (cu : ℕ) (hv : hnfValid a) (ha0 : a 0 = 1)
    (hcu : cu = 88704000 ∨ cu = 177408000)
    (hdvd : (∑ i, a i) * cu ∣ 273030912000000) :
    (∀ i, 0 < i → a i = 0) ∨ (∀ i, a i = hnfS i) ∨
      (cu = 88704000 ∧ a = ![1, 704, 0, 5775, 0, 0, 0, 0, 0]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hnf_valid_mem hv
  rw [hnf_sum_nine, ha0] at hdvd
  have hc : cu ∈ ([88704000, 177408000] : List ℕ) := by simpa using hcu
  rcases hnf_main_digits _ h1 _ h2 _ h3 _ h4 _ h5 _ h6 _ h7 _ h8 cu hc hdvd with
    ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ | ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ |
    ⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8⟩
  · left
    intro i hi
    fin_cases i
    · simp at hi
    all_goals assumption
  · right; left
    intro i
    fin_cases i
    · simpa [hnfS] using ha0
    all_goals simpa [hnfS] using ‹_›
  · right; right
    refine ⟨rfl, ?_⟩
    funext i
    fin_cases i
    · simpa using ha0
    all_goals simpa using ‹_›

set_option synthInstance.maxSize 5000 in
private theorem hnf_bad_digits :
    ∀ x0 ∈ ([0] : List ℕ), ∀ x1 ∈ ([704] : List ℕ), ∀ x2 ∈ ([0, 1100, 2200] : List ℕ),
    ∀ x3 ∈ ([0] : List ℕ), ∀ x4 ∈ ([0, 17600, 35200] : List ℕ),
    ∀ x5 ∈ ([0, 61600, 123200] : List ℕ), ∀ x6 ∈ ([0, 138600, 277200] : List ℕ),
    ∀ x7 ∈ ([0, 177408, 354816] : List ℕ), ∀ x8 ∈ ([0, 369600, 739200] : List ℕ),
      ¬ ((x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) ∣ 6480 * 88704000 ∧
        (6480 * 88704000 / (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8)) ∣ 177408000) := by
  decide

theorem hnf_arith_bad (b : Fin 9 → ℕ) (hv : hnfValid b) (hb0 : b 0 = 0) (h1 : 0 < b 1)
    (hle : ∀ i, (![1, 704, 0, 5775, 0, 0, 0, 0, 0] : Fin 9 → ℕ) i + b i ≤ hnfS i) :
    ¬ ((∑ i, b i) ∣ 6480 * 88704000 ∧ (6480 * 88704000 / ∑ i, b i) ∣ 177408000) := by
  obtain ⟨m1, m2, -, m4, m5, m6, m7, m8⟩ := hnf_valid_mem hv
  have e0 : b 0 ∈ ([0] : List ℕ) := by simpa using hb0
  have e1 : b 1 ∈ ([704] : List ℕ) := by
    have hl := hle 1
    simp [hnfS] at hl m1
    simp
    omega
  have e3 : b 3 ∈ ([0] : List ℕ) := by
    have hl := hle 3
    simp [hnfS] at hl
    simp
    omega
  rw [hnf_sum_nine]
  exact hnf_bad_digits _ e0 _ e1 _ m2 _ e3 _ m4 _ m5 _ m6 _ m7 _ m8

end CFSG.EvenSporadicStandard.Solomon78
