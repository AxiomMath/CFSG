module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.Principal

theorem sq_ne_sq_sub_one {q w : ℤ} (hq : 1 < q) : w ^ 2 ≠ q ^ 2 - 1 := by
  intro h
  have h1 : |w| < q := abs_lt_of_sq_lt_sq (by rw [h]; linarith) (by linarith)
  have h2 : |q - 1| < |w| := sq_lt_sq.mp (by rw [h]; nlinarith)
  rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ q - 1)] at h2
  omega

theorem not_sq_eq_sq_mul_two_mul_sub_one {q a : ℤ} (hq : 1 < q) (ha : 1 < a) :
    a ^ 2 ≠ q ^ 2 * (2 * a - 1) := by
  intro h
  have hdvd : q ∣ a := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨2 * a - 1, h⟩
  obtain ⟨z, rfl⟩ := hdvd
  have hq0 : q ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hz : z ^ 2 = 2 * q * z - 1 :=
    mul_left_cancel₀ hq0 (by linear_combination h)
  exact sq_ne_sq_sub_one hq (w := z - q) (by linear_combination hz)

theorem not_two_part_dvd_half {q : ℕ} {c : ℤ} (hq : 1 < q) (hc : 2 * c = (q : ℤ) ^ 2 + 1) :
    ¬((2 ^ padicValNat 2 (q ^ 2 - 1) : ℕ) : ℤ) ∣ c - 1 := by
  intro hM
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq
  have hne : q ^ 2 - 1 ≠ 0 := by omega
  apply pow_succ_padicValNat_not_dvd (p := 2) hne
  rw [← Int.natCast_dvd_natCast, Nat.cast_sub hq2.le, pow_succ, Nat.cast_mul]
  push_cast
  rw [show (q : ℤ) ^ 2 - 1 = (c - 1) * 2 by linarith]
  exact mul_dvd_mul (by exact_mod_cast hM) (dvd_refl _)

theorem signed_degree_product_two_part_congruence_distinct (q : ℕ) (a b c ε₁ ε₂ ε₃ : ℤ)
    (hq : 1 < q) (_hqodd : Odd q) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hsigns : (ε₁ = -1 ∧ ε₂ = -1 ∧ ε₃ = 1) ∨ (ε₁ = -1 ∧ ε₂ = 1 ∧ ε₃ = -1) ∨
      (ε₁ = 1 ∧ ε₂ = -1 ∧ ε₃ = -1))
    (hsum : 1 + ε₁ * a + ε₂ * b + ε₃ * c = 0) (hprod : a * b = (q : ℤ) ^ 2 * c)
    (hM : ((2 ^ padicValNat 2 (q ^ 2 - 1) : ℕ) : ℤ) ∣ c + ε₃) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hqz : (1 : ℤ) < q := by exact_mod_cast hq
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · subst hab
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact not_sq_eq_sq_mul_two_mul_sub_one hqz ha
        (by linear_combination hprod + (q : ℤ) ^ 2 * hsum)
    · linarith
    · linarith
  · subst hac
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · linarith
    · have hbq : b = (q : ℤ) ^ 2 :=
        mul_left_cancel₀ (by omega : a ≠ 0) (by linear_combination hprod)
      exact not_two_part_dvd_half hq (c := a) (by linarith)
        (by rw [sub_eq_add_neg]; exact hM)
    · linarith
  · subst hbc
    rcases hsigns with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · linarith
    · linarith
    · have haq : a = (q : ℤ) ^ 2 :=
        mul_right_cancel₀ (by omega : b ≠ 0) (by linear_combination hprod)
      exact not_two_part_dvd_half hq (c := b) (by linarith)
        (by rw [sub_eq_add_neg]; exact hM)

theorem padicValNat_order_formula {p : ℕ} [Fact p.Prime] {c d g : ℕ} {A B C E Q : ℤ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) (hQ : Q ≠ 0)
    (h : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 * ((A : ℚ) * B / (C : ℚ) ^ 2) * ((E : ℚ) / Q)) :
    (padicValNat p g : ℤ) = 3 * (padicValNat p c : ℤ) - 2 * (padicValNat p d : ℤ) +
      (padicValInt p A : ℤ) + (padicValInt p B : ℤ) - 2 * (padicValInt p C : ℤ) +
      (padicValInt p E : ℤ) - (padicValInt p Q : ℤ) := by
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hA' : (A : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hA
  have hB' : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB
  have hC' : (C : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hC
  have hE' : (E : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hE
  have hQ' : (Q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hQ
  have hv := congrArg (padicValRat p) h
  rw [padicValRat.mul (mul_ne_zero (div_ne_zero (pow_ne_zero 3 hc') (pow_ne_zero 2 hd'))
      (div_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hC'))) (div_ne_zero hE' hQ'),
    padicValRat.mul (div_ne_zero (pow_ne_zero 3 hc') (pow_ne_zero 2 hd'))
      (div_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hC')),
    padicValRat.div (pow_ne_zero 3 hc') (pow_ne_zero 2 hd'),
    padicValRat.div (mul_ne_zero hA' hB') (pow_ne_zero 2 hC'), padicValRat.div hE' hQ',
    padicValRat.mul hA' hB', padicValRat.pow, padicValRat.pow, padicValRat.pow] at hv
  simp only [padicValRat.of_nat, padicValRat.of_int, Nat.cast_ofNat] at hv
  linarith

theorem pow_three_mul_dvd_of_valuation {p a : ℕ} [Fact p.Prime] {f δ C : ℤ} (ha : 1 ≤ a)
    (hδ : ¬(p : ℤ) ∣ δ) (hC : C ≠ 0) (hfa : (a : ℤ) ≤ padicValInt p f)
    (hCdvd : (p : ℤ) ^ a ∣ f → (p : ℤ) ^ a ∣ C)
    (hineq : 2 * (padicValInt p C : ℤ) + a ≤ padicValInt p f + padicValInt p (f + δ)) :
    (p : ℤ) ^ (3 * a) ∣ f := by
  have hpa : (p : ℤ) ^ a ∣ f := (padicValInt_dvd_iff a f).mpr (Or.inr (by exact_mod_cast hfa))
  have hp1 : (p : ℤ) ∣ f := (dvd_pow_self (p : ℤ) (by omega : a ≠ 0)).trans hpa
  have hβ : padicValInt p (f + δ) = 0 :=
    padicValInt.eq_zero_of_not_dvd fun h => hδ ((dvd_add_right hp1).mp h)
  have hγ : a ≤ padicValInt p C := ((padicValInt_dvd_iff a C).mp (hCdvd hpa)).resolve_left hC
  rw [hβ] at hineq
  exact (padicValInt_dvd_iff (3 * a) f).mpr (Or.inr (by omega))

theorem not_prime_dvd_sign {p : ℕ} (hp : p.Prime) {u : ℤ} (hu : u = 1 ∨ u = -1) :
    ¬(p : ℤ) ∣ u := by
  intro h
  have h1 : (p : ℤ) ∣ 1 := by
    rcases hu with rfl | rfl
    · exact h
    · exact (dvd_neg.mp h)
  have h2 : p ∣ 1 := Int.natCast_dvd_natCast.mp (by exact_mod_cast h1)
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem principal_order_valuation_forces_cubic_degree {p a q : ℕ} (hp : p.Prime) (_hpodd : Odd p)
    (ha : 1 ≤ a) (hq : q = p ^ a) {e δ₁ δ₂ : ℤ} (he : e = 1 ∨ e = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1)
    (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) {f₁ f₂ f₃ : ℤ} {c d g : ℕ} (hf₁ : 0 < f₁) (hf₂ : 0 < f₂)
    (hf₃ : 0 < f₃) (hc : 0 < c) (hd : 0 < d) (_hg : 0 < g) (hf₁δ₁ : 0 < f₁ + δ₁)
    (hf₂δ₂ : 0 < f₂ + δ₂) (hprod : f₁ * f₂ = (q : ℤ) ^ 2 * f₃)
    (hden₁ : f₁ - e * δ₁ * q ≠ 0) (hden₂ : f₂ + e * δ₂ * q ≠ 0)
    (hg₁ : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2) * ((q + e) / q))
    (hg₂ : (g : ℚ) = (c : ℚ) ^ 3 / (d : ℚ) ^ 2 *
      ((f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2) * ((q - e) / q))
    (hval : 3 * (padicValNat p c : ℤ) - 2 * padicValNat p d ≤ padicValNat p g) :
    (q : ℤ) ^ 3 ∣ f₁ ∨ (q : ℤ) ^ 3 ∣ f₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hqpow : (q : ℤ) = (p : ℤ) ^ a := by rw [hq]; push_cast; rfl
  have hq0 : (q : ℤ) ≠ 0 := by rw [hqpow]; exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hvq : padicValInt p (q : ℤ) = a := by rw [padicValInt.of_nat, hq, padicValNat.prime_pow]
  have hpq : (p : ℤ) ∣ (q : ℤ) := by rw [hqpow]; exact dvd_pow_self _ (by omega)
  have hvE : ∀ u : ℤ, (u = 1 ∨ u = -1) → padicValInt p ((q : ℤ) + u) = 0 := fun u hu =>
    padicValInt.eq_zero_of_not_dvd fun h => not_prime_dvd_sign hp hu ((dvd_add_right hpq).mp h)
  have hneE : ∀ u : ℤ, (u = 1 ∨ u = -1) → (q : ℤ) + u ≠ 0 := by
    intro u hu h
    have := hvE u hu
    rw [h] at this
    exact not_prime_dvd_sign hp hu (by
      have hu' : u = -(q : ℤ) := by linarith
      rw [hu']
      exact (dvd_neg.mpr hpq))
  have he' : -e = 1 ∨ -e = -1 := by rcases he with rfl | rfl <;> simp
  have hineq₁ : 2 * padicValInt p (f₁ - e * δ₁ * q) + (a : ℤ) ≤
      padicValInt p f₁ + padicValInt p (f₁ + δ₁) := by
    have h := padicValNat_order_formula (p := p) (A := f₁) (B := f₁ + δ₁)
      (C := f₁ - e * δ₁ * q) (E := q + e) (Q := q) hc.ne' hd.ne' hf₁.ne' hf₁δ₁.ne' hden₁
      (hneE e he) hq0 (by push_cast; exact hg₁)
    rw [hvE e he, hvq] at h
    omega
  have hineq₂ : 2 * padicValInt p (f₂ + e * δ₂ * q) + (a : ℤ) ≤
      padicValInt p f₂ + padicValInt p (f₂ + δ₂) := by
    have h := padicValNat_order_formula (p := p) (A := f₂) (B := f₂ + δ₂)
      (C := f₂ + e * δ₂ * q) (E := q + -e) (Q := q) hc.ne' hd.ne' hf₂.ne' hf₂δ₂.ne' hden₂
      (hneE (-e) he') hq0 (by push_cast; rw [← sub_eq_add_neg]; exact hg₂)
    rw [hvE (-e) he', hvq] at h
    omega
  have hsumα : padicValInt p f₁ + padicValInt p f₂ = 2 * a + padicValInt p f₃ := by
    have h := congrArg (padicValInt p) hprod
    rw [padicValInt.mul hf₁.ne' hf₂.ne', padicValInt.mul (pow_ne_zero 2 hq0) hf₃.ne', sq,
      padicValInt.mul hq0 hq0, hvq] at h
    omega
  have hcube : (q : ℤ) ^ 3 = (p : ℤ) ^ (3 * a) := by rw [hqpow, ← pow_mul, mul_comm]
  rw [hcube]
  rcases (show (a : ℤ) ≤ padicValInt p f₁ ∨ (a : ℤ) ≤ padicValInt p f₂ by omega) with h1 | h2
  · left
    refine pow_three_mul_dvd_of_valuation ha (not_prime_dvd_sign hp hδ₁) hden₁ h1
      (fun hdvd => hdvd.sub ?_) hineq₁
    rw [← hqpow]
    exact Dvd.intro_left _ rfl
  · right
    refine pow_three_mul_dvd_of_valuation ha (not_prime_dvd_sign hp hδ₂) hden₂ h2
      (fun hdvd => hdvd.add ?_) hineq₂
    rw [← hqpow]
    exact Dvd.intro_left _ rfl

end CFSG.Semidihedral.Principal
