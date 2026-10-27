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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

@[expose] def Cont2 {r : ℕ} (δ : Fin r → ℤ) : Prop :=
  ∀ d : ℕ, (∀ i, (d : ℤ) ∣ δ i) → d ∣ 2

theorem dvd_of_cont2 {r : ℕ} {δ : Fin r → ℤ} (hδ : Cont2 δ) {M : ℕ} (hM : Odd M) {c : ℤ}
    (h : ∀ i, (M : ℤ) ∣ c * δ i) : (M : ℤ) ∣ c := by
  by_cases hc : c = 0
  · rw [hc]; exact dvd_zero _
  have hM0 : (M : ℤ) ≠ 0 := by
    have : M ≠ 0 := by rintro rfl; simp at hM
    exact_mod_cast this
  have hpos : 0 < Int.gcd (M : ℤ) c := Int.gcd_pos_of_ne_zero_right _ hc
  obtain ⟨g, m', n', hg, hcop, hMe, hce⟩ := Int.exists_gcd_one' hpos
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hm : ∀ i, m' ∣ δ i := by
    intro i
    have h1 := h i
    rw [hMe, hce] at h1
    have h2 : m' * g ∣ n' * δ i * g := by
      have : n' * g * δ i = n' * δ i * g := by ring
      rwa [this] at h1
    have h3 : m' ∣ n' * δ i := (mul_dvd_mul_iff_right hgz).1 h2
    have hco : IsCoprime m' n' := Int.isCoprime_iff_gcd_eq_one.2 hcop
    exact hco.dvd_of_dvd_mul_left h3
  have hd : m'.natAbs ∣ 2 := hδ _ (fun i => Int.natAbs_dvd.2 (hm i))
  have hodd : Odd m'.natAbs := by
    have : Odd (M : ℤ) := by exact_mod_cast hM
    rw [hMe] at this
    have : Odd m' := (Int.odd_mul.1 this).1
    exact Int.natAbs_odd.2 this
  have h1 : m'.natAbs = 1 := by
    have : m'.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    rcases hodd with ⟨q, hq⟩
    omega
  have : m' = 1 ∨ m' = -1 := by omega
  rcases this with rfl | rfl
  · rw [hMe, hce]; exact ⟨n', by ring⟩
  · rw [hMe, hce]; exact ⟨-n', by ring⟩

section Sep

variable {ι : Type*} {r : ℕ}

theorem odd_isCoprime_two_pow {M : ℕ} (hM : Odd M) (b : ℕ) : IsCoprime (M : ℤ) ((2 : ℤ) ^ b) := by
  refine IsCoprime.pow_right ?_
  obtain ⟨k, rfl⟩ := hM
  exact ⟨1, -(k : ℤ), by push_cast; ring⟩

theorem sep_beta_eq {M : ℕ} (hM : Odd M) {a : ℕ} (ha0 : ¬ (M : ℤ) ∣ a) {X Y : Fin r → ℤ}
    (hXY : X ≠ Y) (hX : Cont2 (X - Y)) (h : ∀ i, (M : ℤ) ∣ (a : ℤ) * (X i - Y i)) : False :=
  ha0 (dvd_of_cont2 (δ := X - Y) hX hM h)

theorem class_sep_gcd (X β : ι → Fin r → ℤ) (M a b : ℕ) (hM : Odd M) (hh : 3 ≤ Nat.gcd a M)
    (hβ : ∀ p q, β p ≠ β q → Cont2 (β p - β q)) (hX : ∀ p q, X p ≠ X q → Cont2 (X p - X q))
    (hinj : ∀ p q, X p = X q → β p = β q → p = q) (hA0 : ¬ (M : ℤ) ∣ a) (p q : ι)
    (h : ∀ i, (M : ℤ) ∣ ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b * β q i)) :
    p = q := by
  by_contra hne
  by_cases hB : β p = β q
  · have hXne : X p ≠ X q := fun hx => hne (hinj p q hx hB)
    refine sep_beta_eq hM hA0 hXne (hX p q hXne) fun i => ?_
    have := h i
    rw [hB] at this
    have e : (a : ℤ) * X p i - 2 ^ b * β q i - (a * X q i - 2 ^ b * β q i) = a * (X p i - X q i) := by
      ring
    rwa [e] at this
  · have hCB := hβ p q hB
    set hh' := Nat.gcd a M with hhdef
    have hhM : (hh' : ℤ) ∣ M := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right a M)
    have hha : (hh' : ℤ) ∣ a := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a M)
    have hhodd : Odd hh' := Odd.of_dvd_nat hM (Nat.gcd_dvd_right a M)
    have hdb : ∀ i, (hh' : ℤ) ∣ (β p - β q) i := by
      intro i
      have h1 := dvd_trans hhM (h i)
      have h2 : (hh' : ℤ) ∣ (a : ℤ) * (X p i - X q i) := dvd_mul_of_dvd_left hha _
      have e : ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b * β q i) =
          a * (X p i - X q i) - 2 ^ b * (β p i - β q i) := by ring
      rw [e] at h1
      have h3 : (hh' : ℤ) ∣ 2 ^ b * (β p i - β q i) := by
        have := dvd_sub h2 h1
        rwa [sub_sub_cancel] at this
      exact (odd_isCoprime_two_pow hhodd b).dvd_of_dvd_mul_left h3
    have := hCB hh' hdb
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem key_cases (M a b : ℕ) (ν μ : ℤ) (hν : ν = 1 ∨ ν = -1 ∨ ν = 2 ∨ ν = -2)
    (hμ : μ = 1 ∨ μ = -1 ∨ μ = 2 ∨ μ = -2) (hcop : Int.gcd ν μ = 1)
    (key : (M : ℤ) ∣ (a : ℤ) * ν - 2 ^ b * μ)
    (hA1 : ¬ (M : ℤ) ∣ (a : ℤ) - 2 ^ b) (hA2 : ¬ (M : ℤ) ∣ (a : ℤ) + 2 ^ b)
    (hA3 : ¬ (M : ℤ) ∣ 2 * (a : ℤ) - 2 ^ b) (hA4 : ¬ (M : ℤ) ∣ 2 * (a : ℤ) + 2 ^ b)
    (hA5 : ¬ (M : ℤ) ∣ (a : ℤ) - 2 ^ (b + 1)) (hA6 : ¬ (M : ℤ) ∣ (a : ℤ) + 2 ^ (b + 1)) : False := by
  have n1 : ∀ u : ℤ, (M : ℤ) ∣ -u → (M : ℤ) ∣ u := fun u h => by simpa using h
  rcases hν with rfl | rfl | rfl | rfl <;> rcases hμ with rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; revert hcop; decide)
    | skip
  · exact hA1 (by have : (a : ℤ) * 1 - 2 ^ b * 1 = a - 2 ^ b := by ring
                  rwa [this] at key)
  · exact hA2 (by have : (a : ℤ) * 1 - 2 ^ b * (-1) = a + 2 ^ b := by ring
                  rwa [this] at key)
  · exact hA5 (by have : (a : ℤ) * 1 - 2 ^ b * 2 = a - 2 ^ (b + 1) := by ring
                  rwa [this] at key)
  · exact hA6 (by have : (a : ℤ) * 1 - 2 ^ b * (-2) = a + 2 ^ (b + 1) := by ring
                  rwa [this] at key)
  · exact hA2 (n1 _ (by have : -((a : ℤ) + 2 ^ b) = (a : ℤ) * (-1) - 2 ^ b * 1 := by ring
                        rwa [this]))
  · exact hA1 (n1 _ (by have : -((a : ℤ) - 2 ^ b) = (a : ℤ) * (-1) - 2 ^ b * (-1) := by ring
                        rwa [this]))
  · exact hA6 (n1 _ (by have : -((a : ℤ) + 2 ^ (b + 1)) = (a : ℤ) * (-1) - 2 ^ b * 2 := by ring
                        rwa [this]))
  · exact hA5 (n1 _ (by have : -((a : ℤ) - 2 ^ (b + 1)) = (a : ℤ) * (-1) - 2 ^ b * (-2) := by ring
                        rwa [this]))
  · exact hA3 (by have : (a : ℤ) * 2 - 2 ^ b * 1 = 2 * a - 2 ^ b := by ring
                  rwa [this] at key)
  · exact hA4 (by have : (a : ℤ) * 2 - 2 ^ b * (-1) = 2 * a + 2 ^ b := by ring
                  rwa [this] at key)
  · exact hA4 (n1 _ (by have : -(2 * (a : ℤ) + 2 ^ b) = (a : ℤ) * (-2) - 2 ^ b * 1 := by ring
                        rwa [this]))
  · exact hA3 (n1 _ (by have : -(2 * (a : ℤ) - 2 ^ b) = (a : ℤ) * (-2) - 2 ^ b * (-1) := by ring
                        rwa [this]))

theorem class_sep_unit (X β : ι → Fin r → ℤ) (M a b : ℕ) (hM : Odd M) (hMbig : 32 < M)
    (hcop : Nat.Coprime a M) (hbdX : ∀ p i, |X p i| ≤ 2) (hbdβ : ∀ p i, |β p i| ≤ 2)
    (hβ : ∀ p q, β p ≠ β q → Cont2 (β p - β q)) (hX : ∀ p q, X p ≠ X q → Cont2 (X p - X q))
    (hinj : ∀ p q, X p = X q → β p = β q → p = q) (hA0 : ¬ (M : ℤ) ∣ a)
    (hA1 : ¬ (M : ℤ) ∣ (a : ℤ) - 2 ^ b) (hA2 : ¬ (M : ℤ) ∣ (a : ℤ) + 2 ^ b)
    (hA3 : ¬ (M : ℤ) ∣ 2 * (a : ℤ) - 2 ^ b) (hA4 : ¬ (M : ℤ) ∣ 2 * (a : ℤ) + 2 ^ b)
    (hA5 : ¬ (M : ℤ) ∣ (a : ℤ) - 2 ^ (b + 1)) (hA6 : ¬ (M : ℤ) ∣ (a : ℤ) + 2 ^ (b + 1))
    (p q : ι)
    (h : ∀ i, (M : ℤ) ∣ ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b * β q i)) :
    p = q := by
  by_contra hne
  have hc : ∀ i, (M : ℤ) ∣ (a : ℤ) * (X p i - X q i) - 2 ^ b * (β p i - β q i) := by
    intro i
    have e : ((a : ℤ) * X p i - 2 ^ b * β p i) - ((a : ℤ) * X q i - 2 ^ b * β q i) =
        a * (X p i - X q i) - 2 ^ b * (β p i - β q i) := by ring
    rw [← e]; exact h i
  by_cases hB : β p = β q
  · have hXne : X p ≠ X q := fun hx => hne (hinj p q hx hB)
    refine sep_beta_eq hM hA0 hXne (hX p q hXne) fun i => ?_
    have := hc i
    rw [hB, sub_self, mul_zero, sub_zero] at this
    exact this
  have hCB := hβ p q hB
  have hMa : IsCoprime (M : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hD : ∀ i j, (X p i - X q i) * (β p j - β q j) - (X p j - X q j) * (β p i - β q i) = 0 := by
    intro i j
    have h1 : (M : ℤ) ∣ (a : ℤ) * ((X p i - X q i) * (β p j - β q j) -
        (X p j - X q j) * (β p i - β q i)) := by
      have e : (a : ℤ) * ((X p i - X q i) * (β p j - β q j) - (X p j - X q j) * (β p i - β q i)) =
          ((a : ℤ) * (X p i - X q i) - 2 ^ b * (β p i - β q i)) * (β p j - β q j) -
          ((a : ℤ) * (X p j - X q j) - 2 ^ b * (β p j - β q j)) * (β p i - β q i) := by ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (hc i) _) (dvd_mul_of_dvd_left (hc j) _)
    have h2 := hMa.dvd_of_dvd_mul_left h1
    have hb : |(X p i - X q i) * (β p j - β q j) - (X p j - X q j) * (β p i - β q i)| < M := by
      have a1 := hbdX p i; have a2 := hbdX q i; have a3 := hbdX p j; have a4 := hbdX q j
      have b1 := hbdβ p i; have b2 := hbdβ q i; have b3 := hbdβ p j; have b4 := hbdβ q j
      rw [abs_le] at a1 a2 a3 a4 b1 b2 b3 b4
      have hM' : (32 : ℤ) < M := by exact_mod_cast hMbig
      rw [abs_lt]
      constructor <;> nlinarith
    exact Int.eq_zero_of_abs_lt_dvd h2 hb
  obtain ⟨i0, hi0⟩ : ∃ i0, β p i0 - β q i0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB (funext fun i => sub_eq_zero.1 (hcon i))
  set ν' := X p i0 - X q i0 with hν'
  set μ' := β p i0 - β q i0 with hμ'
  have hprop : ∀ j, (X p j - X q j) * μ' = ν' * (β p j - β q j) := by
    intro j
    have := hD i0 j
    linarith
  have hgpos : 0 < Int.gcd ν' μ' := Int.gcd_pos_of_ne_zero_right _ hi0
  obtain ⟨g, ν, μ, hg, hcopνμ, hνe, hμe⟩ := Int.exists_gcd_one' hgpos
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hi0
    rw [hμe]; simp
  have hprop' : ∀ j, (X p j - X q j) * μ = ν * (β p j - β q j) := by
    intro j
    have h1 := hprop j
    rw [hνe, hμe] at h1
    have : ((X p j - X q j) * μ) * g = (ν * (β p j - β q j)) * g := by linarith
    exact mul_right_cancel₀ hgz this
  have hcopI : IsCoprime ν μ := Int.isCoprime_iff_gcd_eq_one.2 hcopνμ
  have hμd : ∀ j, μ ∣ β p j - β q j := fun j =>
    hcopI.symm.dvd_of_dvd_mul_left ⟨X p j - X q j, by rw [← hprop' j]; ring⟩
  have hμ2 : μ.natAbs ∣ 2 := hCB _ (fun j => Int.natAbs_dvd.2 (hμd j))
  have hμcases : μ = 1 ∨ μ = -1 ∨ μ = 2 ∨ μ = -2 := by
    have := Nat.le_of_dvd (by norm_num) hμ2
    omega
  by_cases hXe : X p = X q
  ·
    have hν0 : ν = 0 := by
      have h1 := hprop' i0
      rw [hXe, sub_self, zero_mul] at h1
      have : ν * (β p i0 - β q i0) = 0 := h1.symm
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hi0
    have hkey : ∀ j, (M : ℤ) ∣ 2 ^ b * (β p j - β q j) := by
      intro j
      have := hc j
      rw [hXe, sub_self, mul_zero, zero_sub, dvd_neg] at this
      exact this
    have h2 := dvd_of_cont2 hCB hM hkey
    have h3 : (M : ℤ) ∣ 1 := (odd_isCoprime_two_pow hM b).dvd_of_dvd_mul_left
      (by simpa using h2 : (M : ℤ) ∣ 2 ^ b * 1)
    have : M = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3
    omega
  · have hXc := hX p q hXe
    have hνd : ∀ j, ν ∣ X p j - X q j := fun j =>
      hcopI.dvd_of_dvd_mul_right ⟨β p j - β q j, by rw [hprop' j]⟩
    have hν2 : ν.natAbs ∣ 2 := hXc _ (fun j => Int.natAbs_dvd.2 (hνd j))
    have hνcases : ν = 1 ∨ ν = -1 ∨ ν = 2 ∨ ν = -2 := by
      have h1 := Nat.le_of_dvd (by norm_num) hν2
      have hν0 : ν ≠ 0 := by
        rintro rfl
        apply hXe
        funext j
        have := hprop' j
        rw [zero_mul] at this
        rcases mul_eq_zero.1 this with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hμ0
      omega
    have hkey : (M : ℤ) ∣ (a : ℤ) * ν - 2 ^ b * μ := by
      refine dvd_of_cont2 hCB hM fun j => ?_
      show (M : ℤ) ∣ ((a : ℤ) * ν - 2 ^ b * μ) * (β p j - β q j)
      have e : ((a : ℤ) * ν - 2 ^ b * μ) * (β p j - β q j) =
          μ * ((a : ℤ) * (X p j - X q j) - 2 ^ b * (β p j - β q j)) := by
        have := hprop' j
        linear_combination (a : ℤ) * (-this)
      rw [e]
      exact dvd_mul_of_dvd_right (hc j) _
    exact key_cases M a b ν μ hνcases hμcases hcopνμ hkey hA1 hA2 hA3 hA4 hA5 hA6

end Sep

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

