module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
theorem invArith_bezout (a M s : ℤ) (h : ((Int.gcd a M : ℕ) : ℤ) ∣ s) :
    ∃ i : ℤ, M ∣ s + i * a := by
  obtain ⟨k, hk⟩ := h
  have hB := Int.gcd_eq_gcd_ab a M
  refine ⟨-k * Int.gcdA a M, k * Int.gcdB a M, ?_⟩
  linear_combination hk + k * hB

theorem invArith_gcd_dvd (n : ℕ) (a s : ℤ) (ha : ¬ (2 : ℤ) ^ (n + 1) ∣ a)
    (hs : (2 : ℤ) ^ n ∣ s) :
    ((Int.gcd a ((2 : ℤ) ^ (n + 1)) : ℕ) : ℤ) ∣ s := by
  have hG1 : ((Int.gcd a ((2 : ℤ) ^ (n + 1)) : ℕ) : ℤ) ∣ a := Int.gcd_dvd_left ..
  have hG2 : ((Int.gcd a ((2 : ℤ) ^ (n + 1)) : ℕ) : ℤ) ∣ ((2 ^ (n + 1) : ℕ) : ℤ) := by
    rw [show ((2 ^ (n + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) by norm_num]
    exact Int.gcd_dvd_right ..
  have hGnat : Int.gcd a ((2 : ℤ) ^ (n + 1)) ∣ 2 ^ (n + 1) :=
    Int.natCast_dvd_natCast.mp hG2
  obtain ⟨j, hjle, hGj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hGnat
  by_cases hj : j ≤ n
  · have hGn : Int.gcd a ((2 : ℤ) ^ (n + 1)) ∣ 2 ^ n := by
      rw [hGj]
      exact Nat.pow_dvd_pow 2 hj
    have hGn' : ((Int.gcd a ((2 : ℤ) ^ (n + 1)) : ℕ) : ℤ) ∣ (2 : ℤ) ^ n := by
      rw [show (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) by norm_num]
      exact Int.natCast_dvd_natCast.mpr hGn
    exact dvd_trans hGn' hs
  · exfalso
    have hj' : j = n + 1 := by omega
    apply ha
    have hGeq : Int.gcd a ((2 : ℤ) ^ (n + 1)) = 2 ^ (n + 1) := by
      rw [hGj, hj']
    rw [hGeq, show ((2 ^ (n + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) by norm_num] at hG1
    exact hG1

theorem invArith_case_one (m : ℕ) (r s u : ℤ) (hr : r = 4 * u + 1) (h4 : Even s)
    (h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ m ∣ s + i * (r + 1))) : False := by
  obtain ⟨s', hs'⟩ := h4
  have hcop : IsCoprime (2 * u + 1) ((2 : ℤ) ^ m) := by
    apply IsCoprime.pow_right
    exact ⟨1, -u, by ring⟩
  obtain ⟨w, v, hw⟩ := hcop
  refine h5 (-s' * w) ⟨2 * s' * v, ?_⟩
  subst hr hs'
  linear_combination (-2 * s') * hw

theorem invArith_case_three (m : ℕ) (hm : 1 ≤ m) (r s u : ℤ) (hr : r = 4 * u + 3)
    (h3 : (2 : ℤ) ^ m ∣ (r - 1) * s)
    (h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ m ∣ s + i * (r + 1))) :
    (2 : ℤ) ^ m ∣ r + 1 := by
  by_contra hnot
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e1 : (r - 1) * s = 2 * ((2 * u + 1) * s) := by rw [hr]; ring
  have e2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have h2 : (2 : ℤ) ^ n ∣ (2 * u + 1) * s := by
    rw [e1, e2] at h3
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h3
  have hcop : IsCoprime ((2 : ℤ) ^ n) (2 * u + 1) := by
    apply IsCoprime.pow_left
    exact ⟨-u, 1, by ring⟩
  have hs : (2 : ℤ) ^ n ∣ s := hcop.dvd_of_dvd_mul_left h2
  obtain ⟨i, hi⟩ :=
    invArith_bezout (r + 1) ((2 : ℤ) ^ (n + 1)) s (invArith_gcd_dvd n (r + 1) s hnot hs)
  exact h5 i hi

theorem invArith_part1 (m : ℕ) (hm : 1 ≤ m) (r s : ℤ) (hr : Odd r)
    (h3 : (2 : ℤ) ^ m ∣ (r - 1) * s) (h4 : Even s)
    (h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ m ∣ s + i * (r + 1))) :
    (2 : ℤ) ^ m ∣ r + 1 := by
  obtain ⟨t, ht⟩ := hr
  rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact (invArith_case_one m r s u (by omega) h4 h5).elim
  · exact invArith_case_three m hm r s u (by omega) h3 h5

theorem invArith_part2 (m : ℕ) (r s : ℤ) (hr1 : (2 : ℤ) ^ m ∣ r + 1)
    (h3 : (2 : ℤ) ^ m ∣ (r - 1) * s)
    (h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ m ∣ s + i * (r + 1))) :
    ∃ k : ℤ, 2 * s = 2 ^ m * (2 * k + 1) := by
  have h2s : (2 : ℤ) ^ m ∣ 2 * s := by
    have e : 2 * s = (r + 1) * s - (r - 1) * s := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left hr1 s) h3
  obtain ⟨k', hk'⟩ := h2s
  rcases Int.even_or_odd k' with ⟨j, hj⟩ | ⟨k, hk⟩
  · exfalso
    have h2 : 2 * s = 2 * (2 ^ m * j) := by
      rw [hk', hj]
      ring
    have hs : s = 2 ^ m * j := mul_left_cancel₀ two_ne_zero h2
    exact h5 0 ⟨j, by linear_combination hs⟩
  · exact ⟨k, by rw [hk] at hk'; exact hk'⟩

theorem inversion_arith (m : ℕ) (hm : 1 ≤ m) (r s : ℤ) (hr : Odd r)
    (h3 : (2 : ℤ) ^ m ∣ (r - 1) * s) (h4 : Even s)
    (h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ m ∣ s + i * (r + 1))) :
    (2 : ℤ) ^ m ∣ r + 1 ∧ ∃ k : ℤ, 2 * s = 2 ^ m * (2 * k + 1) := by
  have h1 := invArith_part1 m hm r s hr h3 h4 h5
  exact ⟨h1, invArith_part2 m r s h1 h3 h5⟩
end

section
variable {G : Type} [Group G]

structure TwoGroupUniqueInvolution (G : Type) [Group G] (t : G) : Prop where
  two : IsPGroup 2 G
  t_sq : t ^ 2 = 1
  t_ne : t ≠ 1
  uniq : ∀ e : G, e ^ 2 = 1 → e = 1 ∨ e = t

namespace TwoGroupUniqueInvolution

variable {t : G}

theorem t_central (h : TwoGroupUniqueInvolution G t) (g : G) : g * t = t * g := by
  have h1 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, h.t_sq]
    simp
  rcases h.uniq _ h1 with h2 | h2
  · exfalso
    apply h.t_ne
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h2]
    group
  · calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [h2]

theorem pow_half_eq_t (h : TwoGroupUniqueInvolution G t) {a : G} {m : ℕ} (hm : 1 ≤ m) (ha : orderOf a = 2 ^ m) :
    a ^ (2 ^ (m - 1)) = t := by
  have h1 : (a ^ (2 ^ (m - 1))) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ]
    have : m - 1 + 1 = m := by omega
    rw [this, ← ha]
    exact pow_orderOf_eq_one a
  rcases h.uniq _ h1 with h2 | h2
  · exfalso
    have := orderOf_dvd_of_pow_eq_one h2
    rw [ha] at this
    have h3 := Nat.le_of_dvd (by positivity) this
    have h4 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact h2

theorem exists_pow_not_mem_sq_mem (h : TwoGroupUniqueInvolution G t) (A : Subgroup G) {x : G} (hx : x ∉ A) :
    ∃ j : ℕ, x ^ (2 ^ j) ∉ A ∧ (x ^ (2 ^ j)) ^ 2 ∈ A := by
  have hex : ∃ j : ℕ, x ^ (2 ^ j) ∈ A := by
    obtain ⟨k, hk⟩ := h.two x
    exact ⟨k, by rw [hk]; exact A.one_mem⟩
  classical
  let j₀ := Nat.find hex
  have hj₀ : x ^ (2 ^ j₀) ∈ A := Nat.find_spec hex
  have hpos : j₀ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hj₀
    exact hx hj₀
  refine ⟨j₀ - 1, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  have : j₀ - 1 + 1 = j₀ := by omega
  rw [this]
  exact hj₀

theorem invert_of_normalizes (h : TwoGroupUniqueInvolution G t) [Finite G] {a y : G} {n : ℕ}
    (ha : orderOf a = 2 ^ (n + 1)) (hmax : ∀ g : G, orderOf g ≤ 2 ^ (n + 1))
    (hyA : y ∉ Subgroup.zpowers a) (hya : y * a * y⁻¹ ∈ Subgroup.zpowers a)
    (hy2 : y ^ 2 ∈ Subgroup.zpowers a) : y * a * y⁻¹ = a⁻¹ ∧ y ^ 2 = t ∧ 1 ≤ n := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hya
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hy2
  have hat : a ^ (2 ^ n) = t := by
    have := h.pow_half_eq_t (m := n + 1) (by omega) ha
    simpa using this
  have hordZ : ∀ k : ℤ, a ^ k = 1 ↔ (2 : ℤ) ^ (n + 1) ∣ k := by
    intro k
    rw [← orderOf_dvd_iff_zpow_eq_one, ha]
    exact_mod_cast Iff.rfl
  have hconj : ∀ i : ℤ, y * a ^ i * y⁻¹ = a ^ (r * i) := by
    intro i
    rw [← conj_zpow, ← hr, ← zpow_mul]
  have htc := h.t_central
  have ht2z : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    simpa [sq] using h.t_sq
  have htodd : ∀ k : ℤ, t ^ (2 * k + 1) = t := by
    intro k
    rw [zpow_add_one, zpow_mul, ht2z]
    simp
  have hrodd : Odd r := by
    by_contra hcon
    rw [Int.not_odd_iff_even] at hcon
    obtain ⟨r', hr'⟩ := hcon
    have h1 := hconj (2 ^ n : ℕ)
    have h2 : a ^ ((2 ^ n : ℕ) : ℤ) = t := by
      rw [zpow_natCast]
      exact hat
    rw [h2] at h1
    have h3 : y * t * y⁻¹ = t := by
      rw [htc y]
      group
    rw [h3] at h1
    have h4 : a ^ (r * ((2 ^ n : ℕ) : ℤ)) = 1 := by
      rw [hordZ]
      refine ⟨r', ?_⟩
      push_cast
      rw [pow_succ', hr']
      ring
    rw [h4] at h1
    exact h.t_ne h1
  have h3 : (2 : ℤ) ^ (n + 1) ∣ (r - 1) * s := by
    rw [← hordZ]
    have e1 : y * a ^ s * y⁻¹ = a ^ s := by
      rw [hs]
      group
    have e2 := hconj s
    rw [e1] at e2
    have e3 : a ^ (r * s - s) = 1 := by
      rw [zpow_sub, ← e2]
      simp
    have : (r - 1) * s = r * s - s := by ring
    rw [this]
    exact e3
  have h4 : Even s := by
    by_contra hcon
    rw [Int.not_even_iff_odd] at hcon
    obtain ⟨s', hs'⟩ := hcon
    have hy2m : y ^ (2 ^ (n + 1)) = t := by
      have : y ^ (2 ^ (n + 1)) = (y ^ 2) ^ (2 ^ n) := by
        rw [← pow_mul, ← pow_succ']
      rw [this, ← hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hat, hs']
      exact htodd s'
    have hy2m1 : y ^ (2 ^ (n + 1 + 1)) = 1 := by
      rw [pow_succ, pow_mul, hy2m, h.t_sq]
    have hdvd : orderOf y ∣ 2 ^ (n + 1 + 1) := orderOf_dvd_of_pow_eq_one hy2m1
    obtain ⟨j, hj, hjord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hjm : j = n + 1 + 1 := by
      by_contra hne
      have hle : j ≤ n + 1 := by omega
      have : y ^ (2 ^ (n + 1)) = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [hjord]
        exact Nat.pow_dvd_pow 2 hle
      rw [hy2m] at this
      exact h.t_ne this
    have := hmax y
    rw [hjord, hjm] at this
    have h5 : 2 ^ (n + 1) < 2 ^ (n + 1 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h5 : ∀ i : ℤ, ¬ ((2 : ℤ) ^ (n + 1) ∣ s + i * (r + 1)) := by
    intro i hdiv
    have hw : (y * a ^ i) ^ 2 = 1 := by
      have e : (y * a ^ i) ^ 2 = a ^ (s + i * (r + 1)) := by
        have e1 : y * a ^ i = a ^ (r * i) * y := by
          have := hconj i
          calc y * a ^ i = (y * a ^ i * y⁻¹) * y := by group
            _ = a ^ (r * i) * y := by rw [this]
        calc (y * a ^ i) ^ 2 = (y * a ^ i) * (y * a ^ i) := sq _
          _ = a ^ (r * i) * y * (y * a ^ i) := by rw [← e1]
          _ = a ^ (r * i) * (y * y) * a ^ i := by simp only [mul_assoc]
          _ = a ^ (r * i) * y ^ 2 * a ^ i := by rw [← sq]
          _ = a ^ (r * i) * a ^ s * a ^ i := by rw [← hs]
          _ = a ^ (s + i * (r + 1)) := by
            rw [← zpow_add, ← zpow_add]
            congr 1
            ring
      rw [e, hordZ]
      exact hdiv
    rcases h.uniq _ hw with hw1 | hw1
    · apply hyA
      have : y = (y * a ^ i) * a ^ (-i) := by group
      rw [this, hw1, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · apply hyA
      have : y = (y * a ^ i) * a ^ (-i) := by group
      rw [this, hw1, ← hat]
      exact Subgroup.mul_mem _ (by
        rw [← zpow_natCast]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
  obtain ⟨hdvd, k, hk⟩ := inversion_arith (n + 1) (by omega) r s hrodd h3 h4 h5
  have hr1 : y * a * y⁻¹ = a⁻¹ := by
    rw [← hr]
    have : a ^ (r + 1) = 1 := by rw [hordZ]; exact hdvd
    calc a ^ r = a ^ (r + 1) * a⁻¹ := by rw [zpow_add_one]; group
      _ = a⁻¹ := by rw [this, one_mul]
  have hy2t : y ^ 2 = t := by
    rw [← hs]
    have hs2 : s = 2 ^ n * (2 * k + 1) := by
      rw [pow_succ'] at hk
      linarith
    rw [hs2, zpow_mul]
    have e : a ^ ((2 : ℤ) ^ n) = t := by
      have : ((2 : ℤ) ^ n) = ((2 ^ n : ℕ) : ℤ) := by push_cast; rfl
      rw [this, zpow_natCast]
      exact hat
    rw [e]
    exact htodd k
  refine ⟨hr1, hy2t, ?_⟩
  have hy4 : y ^ 4 = 1 := by
    have : y ^ 4 = (y ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hy2t, h.t_sq]
  have hord4 : orderOf y = 2 ^ 2 := by
    apply orderOf_eq_prime_pow
    · rw [pow_one, hy2t]
      exact h.t_ne
    · simpa using hy4
  have := hmax y
  rw [hord4] at this
  by_contra hlt
  have hn0 : n = 0 := by omega
  subst hn0
  omega

theorem zpow_eq_one_iff_dvd {a : G} {n : ℕ} (ha : orderOf a = 2 ^ (n + 1)) (k : ℤ) :
    a ^ k = 1 ↔ (2 : ℤ) ^ (n + 1) ∣ k := by
  rw [← orderOf_dvd_iff_zpow_eq_one, ha]
  exact_mod_cast Iff.rfl

theorem mem_normalizer_of_conj_mem {A : Subgroup G} {y : G} (hf : ∀ g ∈ A, y * g * y⁻¹ ∈ A)
    (hf' : ∀ g ∈ A, y⁻¹ * g * y ∈ A) : y ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hf g, fun hg => ?_⟩
  have := hf' _ hg
  simpa [mul_assoc] using this

theorem not_four_dvd_sq_add_one (w : ℤ) : ¬ (4 : ℤ) ∣ w ^ 2 + 1 := by
  intro h
  have h1 : (((w ^ 2 + 1 : ℤ)) : ZMod 4) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  have h2 : ∀ x : ZMod 4, x ^ 2 + 1 ≠ 0 := by decide
  apply h2 (w : ZMod 4)
  simpa using h1

theorem mem_or_of_mem_normalizer (h : TwoGroupUniqueInvolution G t) [Finite G] {a y : G} {n : ℕ}
    (ha : orderOf a = 2 ^ (n + 1)) (hmax : ∀ g : G, orderOf g ≤ 2 ^ (n + 1)) (hn : 1 ≤ n)
    (hyinv : y * a * y⁻¹ = a⁻¹) {x : G} (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    x ∈ Subgroup.zpowers a ∨ y⁻¹ * x ∈ Subgroup.zpowers a := by
  by_cases hxA : x ∈ Subgroup.zpowers a
  · exact Or.inl hxA
  right
  set A := Subgroup.zpowers a with hA
  have hordZ := zpow_eq_one_iff_dvd ha
  have hconjA : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) → ∀ k : ℤ, g * a ^ k * g⁻¹ ∈ A := by
    intro g hg k
    have hmem : a ^ k ∈ A := Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hmem
  have hyinv' : y⁻¹ * a * y = a⁻¹ := by
    have h1 : y * a⁻¹ * y⁻¹ = a := by rw [← conj_inv, hyinv, inv_inv]
    calc y⁻¹ * a * y = y⁻¹ * (y * a⁻¹ * y⁻¹) * y := by rw [h1]
      _ = a⁻¹ := by group
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_conj_mem
    · intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← conj_zpow, hyinv]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) _
    · intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have : y⁻¹ * a ^ k * y = (y⁻¹ * a * y) ^ k := by
        simpa using (conj_zpow (a := y⁻¹) (b := a) (i := k)).symm
      rw [this, hyinv']
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) _
  obtain ⟨ρ, hρ⟩ := Subgroup.mem_zpowers_iff.mp (hconjA x hx 1)
  rw [zpow_one] at hρ
  have hρpow : ∀ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = a ^ (ρ ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * a * (x ^ (k + 1))⁻¹ = x * (x ^ k * a * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * a ^ (ρ ^ k) * x⁻¹ := by rw [ih]
        _ = (x * a * x⁻¹) ^ (ρ ^ k) := by rw [conj_zpow]
        _ = a ^ (ρ ^ (k + 1)) := by rw [← hρ, ← zpow_mul, pow_succ']
  obtain ⟨j, hj1, hj2⟩ := exists_pow_not_mem_sq_mem h A hxA
  have hx'N : x ^ (2 ^ j) ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hx _
  obtain ⟨hinv1, hinv2, -⟩ := invert_of_normalizes h ha hmax hj1 (by
      have := hconjA _ hx'N 1
      simpa using this) hj2
  have hj0 : j = 0 := by
    by_contra hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have e1 : a ^ (ρ ^ (2 ^ (j' + 1))) = a⁻¹ := by rw [← hρpow, hinv1]
    have e2 : a ^ (ρ ^ (2 ^ (j' + 1)) + 1) = 1 := by
      rw [zpow_add_one, e1]; simp
    have e3 : (2 : ℤ) ^ (n + 1) ∣ ρ ^ (2 ^ (j' + 1)) + 1 := (hordZ _).mp e2
    have e4 : (4 : ℤ) ∣ (2 : ℤ) ^ (n + 1) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact ⟨2 ^ n', by ring⟩
    have e5 : ρ ^ (2 ^ (j' + 1)) = (ρ ^ (2 ^ j')) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e5] at e3
    exact not_four_dvd_sq_add_one _ (e4.trans e3)
  subst hj0
  simp only [pow_zero, pow_one] at hj1 hj2 hinv1 hinv2
  have hcomm : (y⁻¹ * x) * a * (y⁻¹ * x)⁻¹ = a := by
    calc (y⁻¹ * x) * a * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * a * x⁻¹) * y := by group
      _ = y⁻¹ * a⁻¹ * y := by rw [hinv1]
      _ = (y⁻¹ * a * y)⁻¹ := by group
      _ = a := by rw [hyinv']; simp
  by_contra hc
  have hcN : y⁻¹ * x ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hx
  obtain ⟨i, hi1, hi2⟩ := exists_pow_not_mem_sq_mem h A hc
  have hc'N : (y⁻¹ * x) ^ (2 ^ i) ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hcN _
  obtain ⟨hinv3, -, -⟩ := invert_of_normalizes h ha hmax hi1 (by
      have := hconjA _ hc'N 1
      simpa using this) hi2
  have hcomm' : (y⁻¹ * x) ^ (2 ^ i) * a * ((y⁻¹ * x) ^ (2 ^ i))⁻¹ = a := by
    have hc1 : (y⁻¹ * x) * a = a * (y⁻¹ * x) := by
      have := hcomm
      calc (y⁻¹ * x) * a = ((y⁻¹ * x) * a * (y⁻¹ * x)⁻¹) * (y⁻¹ * x) := by group
        _ = a * (y⁻¹ * x) := by rw [this]
    have : Commute ((y⁻¹ * x) ^ (2 ^ i)) a := (Commute.pow_left (hc1) _)
    rw [this.eq]
    group
  rw [hcomm'] at hinv3
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr hinv3
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have hdvd := orderOf_dvd_of_pow_eq_one ha2'
  rw [ha] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have : 2 ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {a g : G}
    (hcase : g * a * g⁻¹ ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  set A := Subgroup.zpowers a with hA
  have hmem : ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hcase _
  let φ : A → A := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
  have hinj : Function.Injective φ := by
    intro x x' hxx'
    have h1 := congrArg Subtype.val hxx'
    simp only [φ] at h1
    exact Subtype.ext (by simpa using h1)
  have hsurj := Finite.surjective_of_injective hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmem x hx, fun hx => ?_⟩
  obtain ⟨⟨w, hw⟩, hww⟩ := hsurj ⟨g * x * g⁻¹, hx⟩
  have h1 := congrArg Subtype.val hww
  simp only [φ] at h1
  have hwx : w = x := by simpa using h1
  rw [← hwx]
  exact hw

theorem normalizer_eq_top (h : TwoGroupUniqueInvolution G t) [Finite G] {a y : G} {n : ℕ}
    (ha : orderOf a = 2 ^ (n + 1)) (hmax : ∀ g : G, orderOf g ≤ 2 ^ (n + 1)) (hn : 2 ≤ n)
    (hyinv : y * a * y⁻¹ = a⁻¹) (hy2 : y ^ 2 = t) :
    Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) = ⊤ := by
  set A := Subgroup.zpowers a with hA
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent G := h.two.isNilpotent
  have hNC := normalizerCondition_of_isNilpotent (G := G)
  have hlt : Subgroup.normalizer (A : Set G) < ⊤ := lt_top_iff_ne_top.mpr hne
  have h1 := hNC _ hlt
  obtain ⟨g, hg, hgn⟩ := SetLike.exists_of_lt h1
  have haN : a ∈ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer (Subgroup.mem_zpowers a)
  have hgaN : g * a * g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hg a).mp haN
  rcases mem_or_of_mem_normalizer h ha hmax (by omega) hyinv hgaN with hcase | hcase
  · exact hgn (mem_normalizer_zpowers_of_conj_mem hcase)
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcase
    have hga : g * a * g⁻¹ = y * a ^ i := by rw [hi]; group
    have hsq : (y * a ^ i) ^ 2 = t := by
      have e0 : y * a ^ i * y⁻¹ = a ^ (-i) := by
        rw [← conj_zpow, hyinv]; simp
      have e1 : y * a ^ i = a ^ (-i) * y := by
        calc y * a ^ i = (y * a ^ i * y⁻¹) * y := by group
          _ = a ^ (-i) * y := by rw [e0]
      calc (y * a ^ i) ^ 2 = (y * a ^ i) * (y * a ^ i) := sq _
        _ = a ^ (-i) * y * (y * a ^ i) := by rw [← e1]
        _ = a ^ (-i) * (y * y) * a ^ i := by simp only [mul_assoc]
        _ = a ^ (-i) * y ^ 2 * a ^ i := by rw [← sq]
        _ = a ^ (-i) * t * a ^ i := by rw [hy2]
        _ = a ^ (-i) * (t * a ^ i) := by rw [mul_assoc]
        _ = a ^ (-i) * (a ^ i * t) := by rw [h.t_central (a ^ i)]
        _ = t := by rw [← mul_assoc, ← zpow_add]; simp
    have h2 : g * a ^ 2 * g⁻¹ = t := by
      rw [← conj_pow, hga, hsq]
    have h4 : g * a ^ 4 * g⁻¹ = 1 := by
      have : g * a ^ 4 * g⁻¹ = (g * a ^ 2 * g⁻¹) ^ 2 := by
        rw [conj_pow, ← pow_mul]
      rw [this, h2, h.t_sq]
    have h5 : a ^ 4 = 1 := by
      have : a ^ 4 = g⁻¹ * (g * a ^ 4 * g⁻¹) * g := by group
      rw [this, h4]; group
    have hdvd := orderOf_dvd_of_pow_eq_one h5
    rw [ha] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 ^ 3 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end TwoGroupUniqueInvolution
end

section
def quatEquiv_pw {G : Type} [Group G] (a : G) {N : ℕ} (i : ZMod N) : G := a ^ (i.val : ℤ)

theorem quatEquiv_zpow_val {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (k : ℤ) : a ^ (((k : ZMod N).val : ℕ) : ℤ) = a ^ k := by
  rw [ZMod.val_intCast, ← ha, zpow_mod_orderOf]

theorem quatEquiv_pw_cast {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (k : ℤ) : quatEquiv_pw a (k : ZMod N) = a ^ k :=
  quatEquiv_zpow_val ha k

theorem quatEquiv_cast_val {N : ℕ} [NeZero N] (i : ZMod N) : ((i.val : ℤ) : ZMod N) = i := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem quatEquiv_pw_add {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (i j : ZMod N) : quatEquiv_pw a (i + j) = quatEquiv_pw a i * quatEquiv_pw a j := by
  have e : (((i.val : ℤ) + (j.val : ℤ) : ℤ) : ZMod N) = i + j := by
    rw [Int.cast_add, quatEquiv_cast_val, quatEquiv_cast_val]
  rw [← e, quatEquiv_pw_cast ha]
  simp only [quatEquiv_pw]
  rw [zpow_add]

theorem quatEquiv_pw_neg {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (i : ZMod N) : quatEquiv_pw a (-i) = (quatEquiv_pw a i)⁻¹ := by
  have e : (((-(i.val : ℤ)) : ℤ) : ZMod N) = -i := by
    rw [Int.cast_neg, quatEquiv_cast_val]
  rw [← e, quatEquiv_pw_cast ha]
  simp only [quatEquiv_pw]
  rw [zpow_neg]

theorem quatEquiv_pw_sub {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (i j : ZMod N) : quatEquiv_pw a (j - i) = (quatEquiv_pw a i)⁻¹ * quatEquiv_pw a j := by
  rw [sub_eq_neg_add, quatEquiv_pw_add ha, quatEquiv_pw_neg ha]

theorem quatEquiv_pw_natCast {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (k : ℕ) : quatEquiv_pw a (k : ZMod N) = a ^ k := by
  have h := quatEquiv_pw_cast ha (k : ℤ)
  rw [Int.cast_natCast] at h
  rw [h, zpow_natCast]

theorem quatEquiv_pw_mem {G : Type} [Group G] {a : G} {N : ℕ} (i : ZMod N) :
    quatEquiv_pw a i ∈ Subgroup.zpowers a :=
  Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), rfl⟩

theorem quatEquiv_pw_inj {G : Type} [Group G] {a : G} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    {i j : ZMod N} (h : quatEquiv_pw a i = quatEquiv_pw a j) : i = j := by
  have hi : i.val < orderOf a := by rw [ha]; exact ZMod.val_lt i
  have hj : j.val < orderOf a := by rw [ha]; exact ZMod.val_lt j
  have h2 : a ^ i.val = a ^ j.val := by
    have h' := h
    simp only [quatEquiv_pw] at h'
    rwa [zpow_natCast, zpow_natCast] at h'
  exact ZMod.val_injective N (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) h2)

theorem quatEquiv_conj_zpow {G : Type} [Group G] {a y : G} (hyinv : y * a * y⁻¹ = a⁻¹) (k : ℤ) :
    y * a ^ k * y⁻¹ = a ^ (-k) := by
  rw [zpow_neg, ← inv_zpow, ← hyinv, conj_zpow]

theorem quatEquiv_zpow_mul_y {G : Type} [Group G] {a y : G} (hyinv : y * a * y⁻¹ = a⁻¹) (k : ℤ) :
    a ^ k * y = y * a ^ (-k) := by
  have h := quatEquiv_conj_zpow hyinv (-k)
  rw [neg_neg] at h
  rw [← h, inv_mul_cancel_right]

theorem quatEquiv_pw_mul_y {G : Type} [Group G] {a y : G} (hyinv : y * a * y⁻¹ = a⁻¹) {N : ℕ}
    (i : ZMod N) : quatEquiv_pw a i * y = y * (quatEquiv_pw a i)⁻¹ := by
  simp only [quatEquiv_pw]
  rw [quatEquiv_zpow_mul_y hyinv, zpow_neg]

theorem quatEquiv_xx_aux {G : Type} [Group G] (y p q : G) (h : p * y = y * p⁻¹) :
    (y * p) * (y * q) = y ^ 2 * (p⁻¹ * q) := by
  rw [sq]
  calc (y * p) * (y * q) = y * (p * y) * q := by simp only [mul_assoc]
    _ = y * (y * p⁻¹) * q := by rw [h]
    _ = (y * y) * (p⁻¹ * q) := by simp only [mul_assoc]

def quatEquiv_phi {G : Type} [Group G] (a y : G) (m : ℕ) : QuaternionGroup (2 ^ m) → G
  | QuaternionGroup.a i => quatEquiv_pw a i
  | QuaternionGroup.xa i => y * quatEquiv_pw a i

theorem quatEquiv_phi_mul {G : Type} [Group G] {a y : G} {m : ℕ} (ha : orderOf a = 2 * 2 ^ m)
    (hyinv : y * a * y⁻¹ = a⁻¹) (hy2 : y ^ 2 = a ^ (2 ^ m))
    (u v : QuaternionGroup (2 ^ m)) :
    quatEquiv_phi a y m (u * v) = quatEquiv_phi a y m u * quatEquiv_phi a y m v := by
  haveI : NeZero (2 * 2 ^ m) := ⟨by positivity⟩
  cases u <;> cases v
  · simp only [quatEquiv_phi, QuaternionGroup.a_mul_a]
    exact quatEquiv_pw_add ha _ _
  · simp only [quatEquiv_phi, QuaternionGroup.a_mul_xa]
    rw [quatEquiv_pw_sub ha, ← mul_assoc (quatEquiv_pw a _) y, quatEquiv_pw_mul_y hyinv, mul_assoc]
  · simp only [quatEquiv_phi, QuaternionGroup.xa_mul_a]
    rw [quatEquiv_pw_add ha, mul_assoc]
  · simp only [quatEquiv_phi, QuaternionGroup.xa_mul_xa]
    rw [add_sub_assoc, quatEquiv_pw_add ha, quatEquiv_pw_sub ha, quatEquiv_pw_natCast ha, ← hy2,
      quatEquiv_xx_aux y _ _ (quatEquiv_pw_mul_y hyinv _)]

theorem quatEquiv_phi_inj {G : Type} [Group G] {a y : G} {m : ℕ} (ha : orderOf a = 2 * 2 ^ m)
    (hyA : y ∉ Subgroup.zpowers a) : Function.Injective (quatEquiv_phi a y m) := by
  haveI : NeZero (2 * 2 ^ m) := ⟨by positivity⟩
  rintro (i | i) (j | j) h
  · simp only [quatEquiv_phi] at h
    rw [quatEquiv_pw_inj ha h]
  · exfalso
    simp only [quatEquiv_phi] at h
    apply hyA
    have hy : y = quatEquiv_pw a i * (quatEquiv_pw a j)⁻¹ := eq_mul_inv_of_mul_eq h.symm
    rw [hy]
    exact mul_mem (quatEquiv_pw_mem i) (inv_mem (quatEquiv_pw_mem j))
  · exfalso
    simp only [quatEquiv_phi] at h
    apply hyA
    have hy : y = quatEquiv_pw a j * (quatEquiv_pw a i)⁻¹ := eq_mul_inv_of_mul_eq h
    rw [hy]
    exact mul_mem (quatEquiv_pw_mem j) (inv_mem (quatEquiv_pw_mem i))
  · simp only [quatEquiv_phi] at h
    have h2 : quatEquiv_pw a i = quatEquiv_pw a j := mul_left_cancel h
    rw [quatEquiv_pw_inj ha h2]

theorem quatEquiv_phi_surj {G : Type} [Group G] {a y : G} {m : ℕ} (ha : orderOf a = 2 * 2 ^ m)
    (hcover : ∀ g : G, g ∈ Subgroup.zpowers a ∨ y⁻¹ * g ∈ Subgroup.zpowers a) :
    Function.Surjective (quatEquiv_phi a y m) := by
  intro g
  rcases hcover g with hg | hg
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨QuaternionGroup.a (k : ZMod (2 * 2 ^ m)), ?_⟩
    simp only [quatEquiv_phi]
    rw [quatEquiv_pw_cast ha k, hk]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨QuaternionGroup.xa (k : ZMod (2 * 2 ^ m)), ?_⟩
    simp only [quatEquiv_phi]
    rw [quatEquiv_pw_cast ha k, hk, mul_inv_cancel_left]

theorem quaternion_equiv_of_cover {G : Type} [Group G] [Finite G] {a y : G} {m : ℕ}
    (ha : orderOf a = 2 * 2 ^ m) (hyinv : y * a * y⁻¹ = a⁻¹) (hy2 : y ^ 2 = a ^ (2 ^ m))
    (hyA : y ∉ Subgroup.zpowers a)
    (hcover : ∀ g : G, g ∈ Subgroup.zpowers a ∨ y⁻¹ * g ∈ Subgroup.zpowers a) :
    Nonempty (G ≃* QuaternionGroup (2 ^ m)) ∧ Nat.card G = 4 * 2 ^ m := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  let f : QuaternionGroup (2 ^ m) →* G :=
    MonoidHom.mk' (quatEquiv_phi a y m) (quatEquiv_phi_mul ha hyinv hy2)
  have hf : Function.Bijective f := ⟨quatEquiv_phi_inj ha hyA, quatEquiv_phi_surj ha hcover⟩
  let e : G ≃* QuaternionGroup (2 ^ m) := (MulEquiv.ofBijective f hf).symm
  refine ⟨⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
end

section
lemma expFour_sq_eq_t {G : Type} [Group G] {t : G} (h4 : ∀ g : G, g ^ 4 = 1)
    (huniq : ∀ e : G, e ^ 2 = 1 → e = 1 ∨ e = t) (x : G) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    x ^ 2 = t := by
  have h2 : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact h4 x
  rcases huniq (x ^ 2) h2 with h | h
  · rcases huniq x h with h' | h'
    · exact absurd h' hx1
    · exact absurd h' hxt
  · exact h

lemma expFour_inv_eq {G : Type} [Group G] {t : G} (ht2 : t ^ 2 = 1) (x : G)
    (hx : x ^ 2 = t) : x⁻¹ = x * t := by
  apply inv_eq_of_mul_eq_one_right
  calc x * (x * t) = x ^ 2 * t := by rw [sq, mul_assoc]
    _ = t * t := by rw [hx]
    _ = t ^ 2 := by rw [sq]
    _ = 1 := ht2

lemma expFour_comm_t {G : Type} [Group G] {t : G} (ht2 : t ^ 2 = 1)
    (h4 : ∀ g : G, g ^ 4 = 1) (huniq : ∀ e : G, e ^ 2 = 1 → e = 1 ∨ e = t)
    (x w : G) (hx1 : x ≠ 1) (hxt : x ≠ t) (hw1 : w ≠ 1) (hwt : w ≠ t)
    (hxw1 : x * w ≠ 1) (hxwt : x * w ≠ t) :
    w * x = x * w * t := by
  have hx2 : x ^ 2 = t := expFour_sq_eq_t h4 huniq x hx1 hxt
  have hw2 : w ^ 2 = t := expFour_sq_eq_t h4 huniq w hw1 hwt
  have hxw2 : (x * w) ^ 2 = t := expFour_sq_eq_t h4 huniq (x * w) hxw1 hxwt
  have hxinv : x⁻¹ = x * t := expFour_inv_eq ht2 x hx2
  have hwinv : w⁻¹ = w * t := expFour_inv_eq ht2 w hw2
  have h1 : x * w * (x * w) = t := by
    rw [← sq]
    exact hxw2
  have key : w * x * w = x := by
    calc w * x * w = x⁻¹ * (x * w * (x * w)) := by group
      _ = x⁻¹ * t := by rw [h1]
      _ = x * t * t := by rw [hxinv]
      _ = x := by rw [mul_assoc, ← sq, ht2, mul_one]
  calc w * x = w * x * w * w⁻¹ := (mul_inv_cancel_right (w * x) w).symm
    _ = x * w⁻¹ := by rw [key]
    _ = x * (w * t) := by rw [hwinv]
    _ = x * w * t := (mul_assoc x w t).symm

theorem cover_of_exponent_four {G : Type} [Group G] {t a y : G}
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htc : ∀ g : G, g * t = t * g)
    (huniq : ∀ e : G, e ^ 2 = 1 → e = 1 ∨ e = t)
    (h4 : ∀ g : G, g ^ 4 = 1)
    (ha : a ^ 2 = t) (hy2 : y ^ 2 = t) (hyA : y ∉ Subgroup.zpowers a) :
    ∀ g : G, g ∈ Subgroup.zpowers a ∨ y⁻¹ * g ∈ Subgroup.zpowers a := by
  intro g
  by_contra hcon
  obtain ⟨hgA, hygA⟩ := not_or.mp hcon
  have haA : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
  have htA : t ∈ Subgroup.zpowers a := by
    rw [← ha]
    exact pow_mem haA 2
  have hA1 : (1 : G) ∈ Subgroup.zpowers a := one_mem _
  have ha1 : a ≠ 1 := by
    intro h
    apply ht1
    rw [← ha, h, one_pow]
  have hat : a ≠ t := by
    intro h
    apply ht1
    rw [← ha, h, ht2]
  have hainv : a⁻¹ = a * t := expFour_inv_eq ht2 a ha
  have hyy : y⁻¹ * y⁻¹ = t := by
    rw [← mul_inv_rev, ← sq, hy2]
    exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have hy1 : y ≠ 1 := by
    intro h
    apply hyA
    rw [h]
    exact hA1
  have hyt : y ≠ t := by
    intro h
    apply hyA
    rw [h]
    exact htA
  have hg1 : g ≠ 1 := by
    intro h
    apply hgA
    rw [h]
    exact hA1
  have hgt : g ≠ t := by
    intro h
    apply hgA
    rw [h]
    exact htA
  have hag1 : a * g ≠ 1 := by
    intro h
    apply hgA
    have hg' : g = a⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    rw [hg']
    exact inv_mem haA
  have hagt : a * g ≠ t := by
    intro h
    apply hgA
    have hg' : g = a := by
      calc g = a⁻¹ * (a * g) := (inv_mul_cancel_left a g).symm
        _ = a⁻¹ * t := by rw [h]
        _ = a * t * t := by rw [hainv]
        _ = a := by rw [mul_assoc, ← sq, ht2, mul_one]
    rw [hg']
    exact haA
  have hga : g * a = a * g * t :=
    expFour_comm_t ht2 h4 huniq a g ha1 hat hg1 hgt hag1 hagt
  have hyg1 : y * g ≠ 1 := by
    intro h
    apply hygA
    have hg' : g = y⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    rw [hg', hyy]
    exact htA
  have hygt : y * g ≠ t := by
    intro h
    apply hygA
    have hg' : g = y⁻¹ * t := by
      calc g = y⁻¹ * (y * g) := (inv_mul_cancel_left y g).symm
        _ = y⁻¹ * t := by rw [h]
    have hyg : y⁻¹ * g = 1 := by
      rw [hg', ← mul_assoc, hyy, ← sq, ht2]
    rw [hyg]
    exact one_mem _
  have hgy : g * y = y * g * t :=
    expFour_comm_t ht2 h4 huniq y g hy1 hyt hg1 hgt hyg1 hygt
  have hay1 : a * y ≠ 1 := by
    intro h
    apply hyA
    have hy' : y = a⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    rw [hy']
    exact inv_mem haA
  have hayt : a * y ≠ t := by
    intro h
    apply hyA
    have hy' : y = a := by
      calc y = a⁻¹ * (a * y) := (inv_mul_cancel_left a y).symm
        _ = a⁻¹ * t := by rw [h]
        _ = a * t * t := by rw [hainv]
        _ = a := by rw [mul_assoc, ← sq, ht2, mul_one]
    rw [hy']
    exact haA
  have hayg1 : a * y * g ≠ 1 := by
    intro h
    apply hygA
    have hg' : g = y⁻¹ * a⁻¹ := by
      rw [← mul_inv_rev]
      exact (inv_eq_of_mul_eq_one_right h).symm
    have hyg : y⁻¹ * g = t * a⁻¹ := by
      rw [hg', ← mul_assoc, hyy]
    rw [hyg]
    exact mul_mem htA (inv_mem haA)
  have haygt : a * y * g ≠ t := by
    intro h
    apply hygA
    have hg' : g = y⁻¹ * a⁻¹ * t := by
      calc g = y⁻¹ * a⁻¹ * (a * y * g) := by group
        _ = y⁻¹ * a⁻¹ * t := by rw [h]
    have hyg : y⁻¹ * g = a⁻¹ := by
      rw [hg', ← mul_assoc, ← mul_assoc, hyy, ← htc a⁻¹, mul_assoc, ← sq, ht2, mul_one]
    rw [hyg]
    exact inv_mem haA
  have hgay : g * (a * y) = a * y * g * t :=
    expFour_comm_t ht2 h4 huniq (a * y) g hay1 hayt hg1 hgt hayg1 haygt
  have K : g * (a * y) = a * y * g := by
    calc g * (a * y) = g * a * y := (mul_assoc g a y).symm
      _ = a * g * t * y := by rw [hga]
      _ = a * (g * (t * y)) := by simp only [mul_assoc]
      _ = a * (g * (y * t)) := by rw [htc y]
      _ = a * (g * y * t) := by simp only [mul_assoc]
      _ = a * (y * g * t * t) := by rw [hgy]
      _ = a * y * g * (t * t) := by simp only [mul_assoc]
      _ = a * y * g := by rw [← sq, ht2, mul_one]
  have h1t : a * y * g * t = a * y * g * 1 := by
    rw [mul_one]
    exact hgay.symm.trans K
  exact ht1 (mul_left_cancel h1t)
end

section
variable {G : Type} [Group G]

namespace TwoGroupUniqueInvolution

variable {t : G}

theorem classify [Finite G] (h : TwoGroupUniqueInvolution G t) (hnc : ¬ IsCyclic G) :
    ∃ n : ℕ, 3 ≤ n ∧ Nat.card G = 2 ^ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨a, hmaxa⟩ := Finite.exists_max (fun g : G => orderOf g)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.two) a
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk00 : k = 0 := by omega
    subst hk00
    have ht1 : orderOf t ≤ 1 := by simpa [hk] using hmaxa t
    have ht2 : orderOf t = 1 := le_antisymm ht1 (orderOf_pos t)
    exact h.t_ne (orderOf_eq_one_iff.mp ht2)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hmax : ∀ g : G, orderOf g ≤ 2 ^ (n + 1) := fun g => hk ▸ hmaxa g
  set A := Subgroup.zpowers a with hA
  have hAtop : A ≠ ⊤ := fun hAt => hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, hAt⟩)
  haveI : Group.IsNilpotent G := h.two.isNilpotent
  have hlt : A < Subgroup.normalizer (A : Set G) :=
    normalizerCondition_of_isNilpotent A (lt_top_iff_ne_top.mpr hAtop)
  obtain ⟨x, hxN, hxA⟩ := SetLike.exists_of_lt hlt
  obtain ⟨j, hj1, hj2⟩ := exists_pow_not_mem_sq_mem h A hxA
  have hyN : x ^ (2 ^ j) ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hxN _
  have hya : x ^ (2 ^ j) * a * (x ^ (2 ^ j))⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hyN a).mp (Subgroup.mem_zpowers a)
  obtain ⟨hyinv, hy2, hn1⟩ := invert_of_normalizes h hk hmax hj1 hya hj2
  generalize x ^ (2 ^ j) = y at hyinv hy2 hj1 hj2 hyN hya
  have hat : a ^ (2 ^ n) = t := by simpa using h.pow_half_eq_t (m := n + 1) (by omega) hk
  have hcover : ∀ g : G, g ∈ A ∨ y⁻¹ * g ∈ A := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn' : n = 1 := by omega
      subst hn'
      have h4 : ∀ g : G, g ^ 4 = 1 := by
        intro g
        obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp h.two) g
        have hle : 2 ^ m ≤ 2 ^ 2 := by simpa [hm] using hmax g
        have hm2 : m ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
        have hdvd : orderOf g ∣ 4 := by
          rw [hm]
          exact (Nat.pow_dvd_pow 2 hm2)
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      exact cover_of_exponent_four h.t_ne h.t_sq h.t_central h.uniq h4 (by simpa using hat) hy2 hj1
    · have htop := normalizer_eq_top h hk hmax hn hyinv hy2
      intro g
      have hg : g ∈ Subgroup.normalizer (A : Set G) := by rw [htop]; trivial
      exact mem_or_of_mem_normalizer h hk hmax hn1 hyinv hg
  have hequiv := quaternion_equiv_of_cover (m := n) (by rw [hk, pow_succ']) hyinv
    (by rw [hy2, hat]) hj1 hcover
  refine ⟨n + 2, by omega, ?_, ?_⟩
  · rw [hequiv.2, pow_add]
    ring
  · have e : n + 2 - 2 = n := by omega
    rw [e]
    exact hequiv.1

end TwoGroupUniqueInvolution

theorem quaternion_of_unique_involution {K : Type} [Group K] [Finite K] {C : Subgroup K}
    (hC : IsPGroup 2 C) {t : K} (ht : t ∈ C) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (huniq : ∀ e ∈ C, e ^ 2 = 1 → e = 1 ∨ e = t) (hnc : ¬ IsCyclic C) :
    ∃ n : ℕ, 3 ≤ n ∧ Nat.card C = 2 ^ n ∧ Nonempty (↥C ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have hUI : TwoGroupUniqueInvolution ↥C ⟨t, ht⟩ :=
    { two := hC
      t_sq := Subtype.ext (by simpa using ht2)
      t_ne := fun h => ht1 (congrArg Subtype.val h)
      uniq := fun e he => by
        have he' : (e : K) ^ 2 = 1 := by
          have := congrArg Subtype.val he
          simpa using this
        rcases huniq e e.2 he' with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h) }
  exact hUI.classify hnc
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
