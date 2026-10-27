module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDual
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Polynomial CFSG.RankThree.PartOne.KCUnitary

namespace CFSG.AGLEmbedding.UnitaryLevi

section Frob
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem tau_aeval (τ : E →+* E) (σ : K →+* K)
    (h : ∀ c, τ (algebraMap K E c) = algebraMap K E (σ c)) (a : K[X]) (y : E) :
    τ (aeval y a) = aeval (τ y) (a.map σ) := by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map]
  congr 1
  ext c
  exact h c

end Frob

section Main
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem dvd_one_add_mul {p q : ℕ} (hp : Odd p) (hq : 1 ≤ q) (hpq : p ∣ q + 1) :
    p ∣ 1 + ((p + 1) / 2) * (q - 1) := by
  obtain ⟨r, rfl⟩ := hp
  obtain ⟨m, hm⟩ := hpq
  have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
  rw [h1]
  refine ⟨(r + 1) * m - 1, ?_⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hq' : q - 1 = (2 * r + 1) * m - 2 := by omega
  have hmpos : 1 ≤ (r + 1) * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [hq']
  have h2 : 2 ≤ (2 * r + 1) * m := by nlinarith
  zify [h2, hmpos]
  have : ((2 * r + 1 : ℕ) : ℤ) = 2 * r + 1 := by push_cast; ring
  ring


theorem dualPoly_eq_self {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {c : K} (hc : c ^ (2 ^ f + 1) = 1) {a : K[X]} (ha : Irreducible a) (hm : a.Monic)
    (hdvd : a ∣ X ^ p - C c) : dualPoly σ a = a := by
  classical
  set q : ℕ := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact zero_ne_one hc
  have : Fact (Irreducible a) := ⟨ha⟩
  have hcard : ∀ x : K, x ^ (q ^ 2) = x := by
    intro x
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hinv : Function.Involutive σ := by
    intro x
    rw [hσ, hσ, ← pow_mul, ← sq]
    exact hcard x
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := hdvd
    have h1 : (X ^ p - C c : K[X]).coeff 0 = a.coeff 0 * b.coeff 0 := by
      rw [hb, mul_coeff_zero]
    have h2 : (X ^ p - C c : K[X]).coeff 0 = -c := by
      simp [coeff_X_pow, hp.ne_zero.symm]
    rw [h0, zero_mul, h2] at h1
    exact hc0 (neg_eq_zero.mp h1)
  let E := AdjoinRoot a
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have : ExpChar E 2 := ExpChar.prime Nat.prime_two
  set θ : E := AdjoinRoot.root a with hθ
  have hθa : aeval θ a = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hθp : θ ^ p = algebraMap K E c := by
    obtain ⟨b, hb⟩ := hdvd
    have h := congrArg (aeval θ) hb
    rw [map_mul, hθa, zero_mul] at h
    simpa [sub_eq_zero] using h
  have hθ0 : θ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hθp
    exact hc0 ((algebraMap K E).injective (by rw [← hθp, map_zero]))
  set ε : E := θ ^ (q + 1) with hε
  have hεp : ε ^ p = 1 := by
    rw [hε, ← pow_mul, mul_comm, pow_mul, hθp, ← map_pow, hc, map_one]
  have hq2 : p ∣ q ^ 2 - 1 := by
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h2, hq1]
      ring
    rw [this]; exact Dvd.dvd.mul_right hpq _
  have hεq : ε ^ (q ^ 2) = ε := by
    obtain ⟨t, ht⟩ := hq2
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : q ^ 2 = p * t + 1 := by omega
    rw [this, pow_succ, pow_mul, hεp, one_pow, one_mul]
  have hθq2 : θ ^ (q ^ 2) = θ * ε ^ (q - 1) := by
    have h2 : q ^ 2 = (q + 1) * (q - 1) + 1 := by
      zify [hq1]
      ring
    rw [h2, pow_succ, pow_mul, mul_comm]
  have hform : ∀ j : ℕ, θ ^ ((q ^ 2) ^ j) = θ * ε ^ (j * (q - 1)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : θ ^ ((q ^ 2) ^ (j + 1)) = (θ ^ ((q ^ 2) ^ j)) ^ (q ^ 2) := by
        rw [pow_succ, pow_mul]
      have e2 : (ε ^ (j * (q - 1))) ^ (q ^ 2) = ε ^ (j * (q - 1)) := by
        rw [← pow_mul, mul_comm, pow_mul, hεq]
      calc θ ^ ((q ^ 2) ^ (j + 1)) = (θ * ε ^ (j * (q - 1))) ^ (q ^ 2) := by rw [e1, ih]
        _ = θ ^ (q ^ 2) * (ε ^ (j * (q - 1))) ^ (q ^ 2) := mul_pow _ _ _
        _ = θ * ε ^ (q - 1) * ε ^ (j * (q - 1)) := by rw [hθq2, e2]
        _ = θ * ε ^ ((j + 1) * (q - 1)) := by rw [mul_assoc, ← pow_add]; congr 2; ring
  let τ : E →+* E := iterateFrobenius E 2 f
  have hτ : ∀ x : E, τ x = x ^ q := fun x => by simp [τ, iterateFrobenius_def, hq]
  have hτK : ∀ c' : K, τ (algebraMap K E c') = algebraMap K E (σ c') := by
    intro c'
    rw [hτ, ← map_pow, hσ]
  let τ2 : E →+* E := iterateFrobenius E 2 (2 * f)
  have hτ2 : ∀ x : E, τ2 x = x ^ (q ^ 2) := fun x => by
    simp [τ2, iterateFrobenius_def, hq, two_mul, pow_add, sq]
  have hτ2K : ∀ c' : K, τ2 (algebraMap K E c') = algebraMap K E ((RingHom.id K) c') := by
    intro c'
    rw [hτ2, ← map_pow, hcard]; rfl
  have hτ2a : ∀ y : E, aeval y a = 0 → aeval (y ^ (q ^ 2)) a = 0 := by
    intro y hy
    have h := tau_aeval τ2 (RingHom.id K) hτ2K a y
    rw [Polynomial.map_id, hy, map_zero, hτ2] at h
    exact h.symm
  have hroot : ∀ j : ℕ, aeval (θ ^ ((q ^ 2) ^ j)) a = 0 := by
    intro j
    induction j with
    | zero => simpa using hθa
    | succ j ih =>
      rw [pow_succ, pow_mul]
      exact hτ2a _ ih
  have hwθ : θ ^ q ≠ 0 := pow_ne_zero _ hθ0
  have hy : θ ^ ((q ^ 2) ^ ((p + 1) / 2)) * θ ^ q = 1 := by
    have hdv := dvd_one_add_mul (hp.odd_of_ne_two hp2) hq1 hpq
    obtain ⟨t, ht⟩ := hdv
    calc θ ^ ((q ^ 2) ^ ((p + 1) / 2)) * θ ^ q
        = (θ * θ ^ q) * ε ^ (((p + 1) / 2) * (q - 1)) := by rw [hform]; ring
      _ = ε ^ (1 + ((p + 1) / 2) * (q - 1)) := by
          have h1 : θ * θ ^ q = ε := by rw [hε, pow_succ, mul_comm]
          rw [h1, pow_add, pow_one]
      _ = 1 := by rw [ht, pow_mul, hεp, one_pow]
  have hya : aeval (θ ^ q)⁻¹ a = 0 := by
    rw [← eq_inv_of_mul_eq_one_left hy]
    exact hroot _
  have hyd : aeval (θ ^ q)⁻¹ (dualPoly σ a) = 0 := by
    let v : Eˣ := Units.mk0 (θ ^ q) hwθ
    have hv1 : ((v⁻¹ : Eˣ) : E) = (θ ^ q)⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; rfl
    have hv2 : (((v⁻¹)⁻¹ : Eˣ) : E) = θ ^ q := by
      rw [inv_inv]; rfl
    have hmapa : aeval (θ ^ q) (a.map σ) = 0 := by
      have h := tau_aeval τ σ hτK a θ
      rw [hθa, map_zero, hτ] at h
      exact h.symm
    have h := aeval_reflect_of_unit (K := K) (v⁻¹) (a.map σ) (N := (a.map σ).natDegree) le_rfl
    rw [hv1, hv2, hmapa, mul_zero] at h
    rw [dualPoly, map_mul, Polynomial.reverse]
    rw [h, mul_zero]
  have e1 : dualPoly σ a = minpoly K (θ ^ q)⁻¹ :=
    minpoly.eq_of_irreducible_of_monic (irreducible_dualPoly hinv ha ha0) hyd
      (monic_dualPoly ha0)
  have e2 : a = minpoly K (θ ^ q)⁻¹ := minpoly.eq_of_irreducible_of_monic ha hya hm
  rw [e1, ← e2]

end Main

theorem reverse_X_sub_C {K : Type*} [Field K] (b : K) :
    (X - C b : K[X]).reverse = 1 - C b * X := by
  have h : (X - C b : K[X]).natDegree = 1 := natDegree_X_sub_C b
  ext i
  rw [coeff_reverse, h]
  rcases i with _ | _ | i
  · rw [revAt_le (by omega)]
    simp [coeff_one, coeff_X]
  · rw [revAt_le (by omega)]
    simp [coeff_one, coeff_X]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_one, coeff_X]

theorem dualPoly_X_sub_C {K : Type*} [Field K] (σ : K →+* K) {l : K} (hl : l ≠ 0) :
    dualPoly σ (X - C l) = X - C (σ l)⁻¹ := by
  have hs : σ l ≠ 0 := (map_ne_zero σ).mpr hl
  rw [dualPoly, coeff_sub, coeff_X_zero, coeff_C_zero, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, reverse_X_sub_C]
  simp only [zero_sub, map_neg, inv_neg]
  have hc : C (σ l)⁻¹ * C (σ l) = 1 := by rw [← C_mul, inv_mul_cancel₀ hs, C_1]
  linear_combination X * hc

end CFSG.AGLEmbedding.UnitaryLevi
