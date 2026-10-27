module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem arith_conds (P B a : ℤ) (hP : 4 ≤ P) (hPe : 2 ∣ P) (hB1 : 1 ≤ B) (hB2 : 2 * B ≤ P)
    (hBp : B = 1 ∨ 2 ∣ B) (ha0 : 0 < a) (haM : a < P - 1) (haB : B < a)
    (hd1 : a + B ≠ P - 1) (hd2 : 2 * a + P ≠ 2 * P - 2) (hd3 : 2 ∣ B → 2 * a + B ≠ 2 * P - 2)
    (hd4 : a + 2 * B ≠ P - 1) (hd5 : a + 1 ≠ P - 1)
    (hf1 : 2 * a ≠ P) (hf2 : 2 * a ≠ B) (hf3 : a ≠ 2 * B) (hf4 : a ≠ 1) :
    ¬ (P - 1 ∣ a) ∧ ¬ (P - 1 ∣ a - B) ∧ ¬ (P - 1 ∣ a + B) ∧ ¬ (P - 1 ∣ 2 * a - B) ∧
      ¬ (P - 1 ∣ 2 * a + B) ∧ ¬ (P - 1 ∣ a - 2 * B) ∧ ¬ (P - 1 ∣ a + 2 * B) := by
  have hM : 3 ≤ P - 1 := by omega
  obtain ⟨Q, hQ⟩ := hPe
  have hBp' : B = 1 ∨ ∃ C, B = 2 * C := by
    rcases hBp with h | ⟨C, hC⟩
    · exact Or.inl h
    · exact Or.inr ⟨C, hC⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 1 := by nlinarith
    omega
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 1 := by nlinarith
    omega
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 2 := by nlinarith
    have : c = 1 := by omega
    subst this
    apply hd1; linarith
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 2 := by nlinarith
    have : c = 1 := by omega
    subst this
    rcases hBp' with rfl | ⟨C, hC⟩
    · apply hf1; omega
    · omega
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 3 := by nlinarith
    have : c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl
    · rcases hBp' with rfl | ⟨C, hC⟩
      · apply hd2; omega
      · omega
    · rcases hBp' with rfl | ⟨C, hC⟩
      · omega
      · apply hd3 ⟨C, by omega⟩; omega
  · rintro ⟨c, hc⟩
    have h1 : -2 < c := by nlinarith
    have h2 : c < 1 := by nlinarith
    have : c = 0 ∨ c = -1 := by omega
    rcases this with rfl | rfl
    · apply hf3; omega
    · apply hf4; omega
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by nlinarith
    have h2 : c < 3 := by nlinarith
    have : c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl
    · apply hd4; omega
    · apply hd5; omega

theorem testBit_sum_of_mem {J' : Finset ℕ} {j : ℕ} (hj : j ∈ J') :
    (∑ i ∈ J', 2 ^ i).testBit j = true := by
  have h := Finset.toFinset_bitIndices_sum_two_pow J'
  have : j ∈ (∑ i ∈ J', 2 ^ i).bitIndices.toFinset := by rw [h]; exact hj
  rw [List.mem_toFinset, Nat.mem_bitIndices] at this
  exact this

theorem sum_ne_two_pow {J' : Finset ℕ} (h2 : 2 ≤ J'.card) (c : ℕ) : ∑ i ∈ J', 2 ^ i ≠ 2 ^ c := by
  intro h
  have h1 : ∀ j ∈ J', j = c := by
    intro j hj
    have := testBit_sum_of_mem hj
    rw [h, Nat.testBit_two_pow] at this
    exact (by simpa using this : c = j).symm
  have : J'.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => (h1 a ha).trans (h1 b hb).symm
  omega

theorem pair_le_sum {J' : Finset ℕ} (h2 : 2 ≤ J'.card) {b : ℕ} (hb : b ∈ J') :
    2 ^ b < ∑ i ∈ J', 2 ^ i := by
  obtain ⟨c, hc, hcb⟩ : ∃ c ∈ J', c ≠ b := by
    by_contra hcon
    push Not at hcon
    have : J'.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => (hcon x hx).trans (hcon y hy).symm
    omega
  have hsub : ({b, c} : Finset ℕ) ⊆ J' := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h1 := Finset.sum_le_sum_of_subset (f := fun i => 2 ^ i) hsub
  rw [Finset.sum_pair (Ne.symm hcb)] at h1
  have : 0 < 2 ^ c := by positivity
  omega

theorem digit_conds {n : ℕ} (hn : 2 ≤ n) {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) {b : ℕ}
    (hb : b ∈ J') (h2 : 2 ≤ J'.card) (hlt : ∑ i ∈ J', 2 ^ i < 2 ^ n - 1)
    (hD3 : ∀ c < n, ∑ i ∈ J', 2 ^ i + 2 ^ c ≠ 2 ^ n - 1) :
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ)) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ b) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) + 2 ^ b) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ 2 * ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ b) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ 2 * ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) + 2 ^ b) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) - 2 ^ (b + 1)) ∧
    ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) + 2 ^ (b + 1)) := by
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hbn : b < n := hJ' b hb
  have hP1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have hcast : (((2 ^ n - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub hP1]; push_cast; ring
  rw [hcast]
  have e2 : (2 : ℤ) ^ (b + 1) = 2 * 2 ^ b := by ring
  rw [e2]
  have hP4 : (4 : ℤ) ≤ 2 ^ n := by
    have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h' : ((2 : ℕ) ^ 2 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hPe : (2 : ℤ) ∣ 2 ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m, by ring⟩
  have hB1 : (1 : ℤ) ≤ 2 ^ b := by exact_mod_cast Nat.one_le_two_pow
  have hB2 : 2 * (2 : ℤ) ^ b ≤ 2 ^ n := by
    have : 2 ^ (b + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hbn
    have h' : ((2 ^ (b + 1) : ℕ) : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'
    have e : (2 : ℤ) ^ (b + 1) = 2 * 2 ^ b := by ring
    linarith
  have hBp : (2 : ℤ) ^ b = 1 ∨ 2 ∣ (2 : ℤ) ^ b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · left; simp [h0]
    · right
      obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      exact ⟨2 ^ m, by ring⟩
  have ha0 : (0 : ℤ) < a := by
    have := pair_le_sum h2 hb
    have h' : 0 < 2 ^ b := by positivity
    exact_mod_cast (by omega : 0 < a)
  have haM : (a : ℤ) < 2 ^ n - 1 := by
    have : (a : ℤ) < ((2 ^ n - 1 : ℕ) : ℤ) := by exact_mod_cast hlt
    rwa [hcast] at this
  have haB : (2 : ℤ) ^ b < a := by exact_mod_cast pair_le_sum h2 hb
  have hne : ∀ (x y : ℤ), (∀ c < n, (a : ℤ) + 2 ^ c ≠ 2 ^ n - 1) → True := fun _ _ _ => trivial
  have hD : ∀ c < n, (a : ℤ) + 2 ^ c ≠ 2 ^ n - 1 := by
    intro c hc h
    apply hD3 c hc
    have : ((a + 2 ^ c : ℕ) : ℤ) = ((2 ^ n - 1 : ℕ) : ℤ) := by rw [hcast]; push_cast; linarith
    exact_mod_cast this
  have hf : ∀ c : ℕ, (a : ℤ) ≠ 2 ^ c := by
    intro c h
    exact sum_ne_two_pow h2 c (by exact_mod_cast h)
  have hn1 : n - 1 < n := by omega
  have hP : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  refine arith_conds ((2 : ℤ) ^ n) ((2 : ℤ) ^ b) a hP4 hPe hB1 hB2 hBp ha0 haM haB
    (hD b hbn) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro h
    apply hD (n - 1) hn1
    rw [hP] at h ⊢
    linarith
  · rintro ⟨C, hC⟩ h
    have hb1 : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; simp at hC; omega
      · omega
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    apply hD m (by omega)
    have : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [this] at h
    linarith
  · by_cases hb1 : b + 1 < n
    · have := hD (b + 1) hb1
      rwa [e2] at this
    · intro h
      have : b + 1 = n := by omega
      have h' : (2 : ℤ) * 2 ^ b = 2 ^ n := by rw [← this]; ring
      linarith
  · have := hD 0 (by omega)
    simpa using this
  · intro h
    apply hf (n - 1)
    rw [hP] at h
    linarith
  · intro h
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; simp at h; omega
    · obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      apply hf m
      have : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [this] at h
      linarith
  · intro h
    apply hf (b + 1)
    rw [h]; ring
  · intro h
    apply hf 0
    simpa using h

theorem sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem digit_D3 {n : ℕ} {J' : Finset ℕ} (hcard : J'.card + 2 ≤ n) :
    ∀ c < n, ∑ i ∈ J', 2 ^ i + 2 ^ c ≠ 2 ^ n - 1 := by
  intro c hc h
  have h1 := sum_range_two_pow n
  have h2 : ∑ i ∈ (Finset.range n).erase c, 2 ^ i + 2 ^ c = ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_erase_add _ _ (Finset.mem_range.2 hc)
  have h3 : ∑ i ∈ J', 2 ^ i = ∑ i ∈ (Finset.range n).erase c, 2 ^ i := by omega
  have h4 : J' = (Finset.range n).erase c := Finset.equivBitIndices.symm.injective h3
  rw [h4, Finset.card_erase_of_mem (Finset.mem_range.2 hc), Finset.card_range] at hcard
  omega

theorem gcd_ge_three {n g a : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (ht2 : 2 ≤ n / g)
    (hper : (2 ^ n - 1) ∣ (2 ^ g - 1) * a) (ha : 0 < a) : 3 ≤ Nat.gcd a (2 ^ n - 1) := by
  obtain ⟨t, rfl⟩ := hgn
  have ht : g * t / g = t := Nat.mul_div_cancel_left t (by omega)
  rw [ht] at ht2
  have h2g : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hdvd : 2 ^ g - 1 ∣ 2 ^ (g * t) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 t
    rwa [one_pow, ← pow_mul] at this
  obtain ⟨gh, hgh⟩ := hdvd
  have hpos : 0 < 2 ^ g - 1 := by omega
  have hghdvd : gh ∣ a := by
    rw [hgh] at hper
    exact (Nat.dvd_of_mul_dvd_mul_left hpos (by simpa [mul_comm] using hper))
  have hghM : gh ∣ 2 ^ (g * t) - 1 := ⟨2 ^ g - 1, by rw [hgh]; ring⟩
  have hgcd : gh ∣ Nat.gcd a (2 ^ (g * t) - 1) := Nat.dvd_gcd hghdvd hghM
  have hgpos : 0 < Nat.gcd a (2 ^ (g * t) - 1) := Nat.gcd_pos_of_pos_left _ ha
  have hle : gh ≤ Nat.gcd a (2 ^ (g * t) - 1) := Nat.le_of_dvd hgpos hgcd
  have h3 : 2 ^ g + 1 ≤ gh := by
    have h4 : (2 ^ g - 1) * (2 ^ g + 1) ≤ (2 ^ g - 1) * gh := by
      rw [← hgh]
      have h5 : 2 ^ (2 * g) ≤ 2 ^ (g * t) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have h6 : (2 ^ g - 1) * (2 ^ g + 1) = 2 ^ (2 * g) - 1 := by
        obtain ⟨y, hy⟩ : ∃ y, 2 ^ g = y + 1 := ⟨2 ^ g - 1, by omega⟩
        rw [pow_mul', pow_two, hy]
        simp only [Nat.add_sub_cancel]
        rw [show (y + 1) * (y + 1) - 1 = y * (y + 2) by
          rw [show (y + 1) * (y + 1) = y * (y + 2) + 1 by ring]; simp]
      rw [h6]
      omega
    exact Nat.le_of_mul_le_mul_left h4 hpos
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc


