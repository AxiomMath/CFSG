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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.Uniqueness

namespace Sec128

theorem arith_a {Ω M Cz au q Q : ℕ} (hq : 2 ≤ q) (hCz : 0 < Cz)
    (hX : Ω * M = Cz * au) (hM : M = (q - 1) * Cz)
    (hau : au = (q - 1) * (Q + 1) * (Q * (q - 1) + 1)) :
    Ω = (Q + 1) * (Q * (q - 1) + 1) := by
  have hq1 : 0 < q - 1 := by omega
  have hpos : 0 < (q - 1) * Cz := Nat.mul_pos hq1 hCz
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (q - 1) * Cz * Ω = Ω * M := by rw [hM]; ring
    _ = Cz * au := hX
    _ = (q - 1) * Cz * ((Q + 1) * (Q * (q - 1) + 1)) := by rw [hau]; ring

theorem arith_b {Ω M Cz Cu CuM uM V au az q Q : ℕ} (hq : 2 ≤ q) (hM0 : 0 < M)
    (hX : Ω * M = Cz * au + Cu * az) (hMz : M = (q ^ 2 - 1) * Cz) (hCu : Cu = (Q + 1) * CuM)
    (hMu : M = uM * CuM) (haz : az = q * V) (hV : V * (q ^ 2 - 1) = uM * (q - 1))
    (hau : au = (q - 1) * (Q + 1) * (Q * (q - 1) + 1)) :
    Ω * (q + 1) = (Q + 1) * (Q * (q - 1) + q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hq2 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  rw [hq2] at hMz hV
  have key : Ω * M * (r * (r + 2)) = M * ((Q + 1) * (Q * r + (r + 1) + 1) * r) := by
    calc Ω * M * (r * (r + 2)) = (Cz * au + Cu * az) * (r * (r + 2)) := by rw [hX]
      _ = (r * (r + 2) * Cz) * au + (Q + 1) * (r + 1) * CuM * (V * (r * (r + 2))) := by
          rw [hCu, haz]; ring
      _ = M * au + (Q + 1) * (r + 1) * CuM * (uM * r) := by rw [← hMz, hV]
      _ = M * au + (Q + 1) * (r + 1) * r * (uM * CuM) := by ring
      _ = M * ((Q + 1) * (Q * r + (r + 1) + 1) * r) := by rw [← hMu, hau]; ring
  have hpos : 0 < M * r := Nat.mul_pos hM0 (by omega)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc M * r * (Ω * (r + 1 + 1)) = Ω * M * (r * (r + 2)) := by ring
    _ = _ := key
    _ = M * r * ((Q + 1) * (Q * r + (r + 1) + 1)) := by ring

theorem arith_linear {Ω q : ℕ} (hq : 1 ≤ q)
    (h : Ω * (q + 1) = (q ^ 1 + 1) * (q ^ 1 * (q - 1) + q + 1)) : Ω = q ^ 2 + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_one] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < r + 1 + 1 by omega)
  rw [h]; ring

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  induction a with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
    omega

theorem arith_suzuki {Ω a : ℕ}
    (h : Ω * (2 ^ (2 * a + 1) + 1) =
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * ((2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) +
        2 ^ (2 * a + 1) + 1)) : False := by
  have h3 := two_pow_odd_mod_three a
  set q := 2 ^ (2 * a + 1) with hq
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rw [hk] at h
  have e1 : 3 * k + 2 - 1 = 3 * k + 1 := by omega
  rw [e1] at h
  set A := 3 * k ^ 2 + 4 * k + 1
  set B := 9 * k ^ 3 + 15 * k ^ 2 + 9 * k + 2
  have e : ((3 * k + 2) ^ 2 + 1) * ((3 * k + 2) ^ 2 * (3 * k + 1) + (3 * k + 2) + 1) =
      3 * (3 * A * B + A + 2 * B) + 2 := by ring
  rw [e, show Ω * (3 * k + 2 + 1) = 3 * (Ω * (k + 1)) by ring] at h
  omega

theorem arith_unitary {Ω q p : ℕ} (hq : 2 ≤ q) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1)
    (hΩ : Ω ≡ 2 [MOD p]) (h : Ω * (q + 1) = (q ^ 3 + 1) * (q ^ 3 * (q - 1) + q + 1)) : False := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  have hΩ' : Ω = (r ^ 2 + r + 1) * ((r + 1) ^ 3 * r + (r + 1) + 1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < r + 1 + 1 by omega)
    rw [h]; ring
  have key : (Ω : ℤ) - 6 = ((r : ℤ) + 1 + 1) *
      ((r : ℤ) ^ 5 + 2 * (r : ℤ) ^ 4 + 3 * (r : ℤ) ^ 3 + 2 * (r : ℤ) ^ 2 + 3 * (r : ℤ) - 2) := by
    rw [hΩ']; push_cast; ring
  have h1 : (p : ℤ) ∣ (Ω : ℤ) - 6 := by
    rw [key]
    exact Dvd.dvd.mul_right (by exact_mod_cast hpq) _
  have h2 : (p : ℤ) ∣ (2 : ℤ) - Ω := by
    have := (Nat.modEq_iff_dvd.mp hΩ)
    simpa using this
  have h4 : (p : ℤ) ∣ 4 := by
    have := dvd_add h1 h2
    have e : (Ω : ℤ) - 6 + (2 - Ω) = -4 := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  have h4' : p ∣ 2 ^ 2 := by exact_mod_cast h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4'))

theorem arith_values (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 1 + 1) * (q ^ 1 * (q - 1) + 1) = q ^ 3 + 1 ∧
    (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) + q ^ 4 = q ^ 5 + q ^ 3 + 1 ∧
    (q ^ 3 + 1) * (q ^ 3 * (q - 1) + 1) + q ^ 6 = q ^ 7 + q ^ 4 + 1 ∧
    (q ^ 1 + 1) * (q ^ 1 * ((q - 1) * 1)) + (q ^ 1 + 1) = (q ^ 1 + 1) * (q ^ 1 * (q - 1) + 1) ∧
    (q ^ 2 + 1) * (q ^ 2 * ((q - 1) * 1)) + (q ^ 2 + 1) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

theorem arith_ne {q Ω : ℕ} (hq : 2 ≤ q) (h1 : Ω = q ^ 3 + 1)
    (h2 : Ω + q ^ 6 = q ^ 7 + q ^ 4 + 1) : False := by
  subst h1
  have h6 : 2 * q ^ 6 ≤ q ^ 7 := by
    rw [show q ^ 7 = q * q ^ 6 by ring]; exact Nat.mul_le_mul_right _ hq
  have h7 : q ^ 3 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem factorization_two_pow_mul_odd {k r : ℕ} (hr : Odd r) :
    (2 ^ k * r).factorization 2 = k := by
  have hr0 : r ≠ 0 := by rintro rfl; exact absurd hr (by decide)
  rw [Nat.factorization_mul (by positivity) hr0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    add_zero]

theorem factorization_card {Ω D k r : ℕ} (hk : 1 ≤ k) (hr : Odd r) (hΩ : Ω = 2 ^ k * r + 1)
    (hD : 0 < D) : (Ω * ((Ω - 1) * D)).factorization 2 = k + D.factorization 2 := by
  have hΩ1 : Ω - 1 = 2 ^ k * r := by omega
  have hodd : ¬ 2 ∣ Ω := by
    rw [hΩ]; intro h2
    have : 2 ∣ 2 ^ k * r := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) r
    omega
  have hΩ0 : Ω ≠ 0 := by omega
  have hr0 : r ≠ 0 := by rintro rfl; exact absurd hr (by decide)
  rw [hΩ1, Nat.factorization_mul hΩ0 (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, zero_add,
    Nat.factorization_mul (by positivity) hD.ne', Finsupp.add_apply,
    factorization_two_pow_mul_odd hr]

theorem arith_j1 {X0 M D LD L q i : ℕ} (hq : 2 ≤ q) (hD : 0 < D) (hi : i = 1 ∨ i = 2)
    (hXM : (q + 1) * M = X0) (hMD : q * D = M) (hprod : LD * (q - 1) = L * D)
    (hL : L = (q ^ i + 1) * (q ^ i * ((q - 1) * 1))) (hle : LD ≤ X0) : LD = X0 := by
  have hq1 : 0 < q - 1 := by omega
  have hLD : LD = (q ^ i + 1) * q ^ i * D := by
    apply Nat.eq_of_mul_eq_mul_right hq1
    rw [hprod, hL]; ring
  subst hXM hMD
  rcases hi with rfl | rfl
  · rw [hLD]; ring
  · exfalso
    rw [hLD] at hle
    have h4 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
    have h1 : (q + 1) * q < (q ^ 2 + 1) * q ^ 2 := by nlinarith
    have h2 : (q + 1) * q * D < (q ^ 2 + 1) * q ^ 2 * D := Nat.mul_lt_mul_of_pos_right h1 hD
    have h3 : (q + 1) * (q * D) = (q + 1) * q * D := by ring
    omega

theorem arith_omega_b (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) = q ^ 3 * (q * (q - 1) + 1) + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

theorem arith_omega_c (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 3 + 1) * (q ^ 3 * (q - 1) + 1) = q ^ 4 * (q ^ 2 * (q - 1) + 1) + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

theorem odd_mul_add_one {q : ℕ} (hq : Even q) (a : ℕ) : Odd (q * a + 1) :=
  (hq.mul_right a).add_one

end Sec128

end CFSG.GH74.Uniqueness
