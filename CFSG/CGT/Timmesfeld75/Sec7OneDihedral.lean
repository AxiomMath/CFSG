module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

namespace CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G] {d e : G}

theorem dihedral_inv (hd : d * d = 1) (he : e * e = 1) : (d * e)⁻¹ = e * d := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right he, inv_eq_of_mul_eq_one_right hd]

theorem dihedral_conj_pow (hd : d * d = 1) (he : e * e = 1) (j : ℕ) :
    d * (d * e) ^ j * d = ((d * e) ^ j)⁻¹ := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have h1 : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [dihedral_inv hd he, hdi]
    calc d * (d * e) * d = (d * d) * e * d := by group
      _ = e * d := by rw [hd, one_mul]
  have h2 : (d * (d * e) * d⁻¹) ^ j = d * (d * e) ^ j * d⁻¹ := conj_pow
  rw [h1, hdi, inv_pow] at h2
  exact h2.symm

theorem dihedral_conj_pow' (hd : d * d = 1) (he : e * e = 1) (j : ℕ) :
    e * (d * e) ^ j * e = ((d * e) ^ j)⁻¹ := by
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have h1 : e * (d * e) * e⁻¹ = (d * e)⁻¹ := by
    rw [dihedral_inv hd he, hei]
    calc e * (d * e) * e = e * d * (e * e) := by group
      _ = e * d := by rw [he, mul_one]
  have h2 : (e * (d * e) * e⁻¹) ^ j = e * (d * e) ^ j * e⁻¹ := conj_pow
  rw [h1, hei, inv_pow] at h2
  exact h2.symm

theorem dihedral_center_comm (hd : d * d = 1) (he : e * e = 1) {k : ℕ}
    (hk : (d * e) ^ (2 * k) = 1) :
    d * (d * e) ^ k = (d * e) ^ k * d ∧ e * (d * e) ^ k = (d * e) ^ k * e := by
  have hz : (d * e) ^ k * (d * e) ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hk
  have hzi : ((d * e) ^ k)⁻¹ = (d * e) ^ k := inv_eq_of_mul_eq_one_right hz
  constructor
  · have h := dihedral_conj_pow hd he k
    rw [hzi] at h
    calc d * (d * e) ^ k = d * (d * e) ^ k * (d * d) := by rw [hd, mul_one]
      _ = (d * (d * e) ^ k * d) * d := by group
      _ = (d * e) ^ k * d := by rw [h]
  · have h := dihedral_conj_pow' hd he k
    rw [hzi] at h
    calc e * (d * e) ^ k = e * (d * e) ^ k * (e * e) := by rw [he, mul_one]
      _ = (e * (d * e) ^ k * e) * e := by group
      _ = (d * e) ^ k * e := by rw [h]

theorem dihedral_center_mul_conj (hd : d * d = 1) (he : e * e = 1) {k : ℕ} (hodd : Odd k)
    (hk : (d * e) ^ (2 * k) = 1) :
    (d * e) ^ k * d = (d * e) ^ ((k + 1) / 2) * e * ((d * e) ^ ((k + 1) / 2))⁻¹ := by
  obtain ⟨c, hc⟩ := hodd
  have hj : (k + 1) / 2 = c + 1 := by omega
  rw [hj]
  set r := d * e with hr
  set g := r ^ (c + 1) with hg
  have hgr : Commute g r := (Commute.refl r).pow_left (c + 1)
  have hz : r ^ k * r ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hk
  have hzi : (r ^ k)⁻¹ = r ^ k := inv_eq_of_mul_eq_one_right hz
  have hdz : d * r ^ k = r ^ k * d := (dihedral_center_comm hd he hk).1
  have hgd : g * d = d * g⁻¹ := by
    have h := dihedral_conj_pow hd he (c + 1)
    rw [← hg] at h
    calc g * d = d * (d * g * d) := by
          calc g * d = (d * d) * g * d := by rw [hd, one_mul]
            _ = d * (d * g * d) := by group
      _ = d * g⁻¹ := by rw [h]
  have hee : e = d * r := by rw [hr]; calc e = (d * d) * e := by rw [hd, one_mul]
    _ = d * (d * e) := by group
  have hg2 : g * g = r ^ k * r := by
    rw [hg, ← pow_add, show c + 1 + (c + 1) = k + 1 by omega, pow_succ]
  have hmain : g * e * g⁻¹ = r ^ k * d := by
    calc g * e * g⁻¹ = g * (d * r) * g⁻¹ := by rw [← hee]
      _ = (g * d) * r * g⁻¹ := by group
      _ = (d * g⁻¹) * r * g⁻¹ := by rw [hgd]
      _ = d * (g⁻¹ * r * g⁻¹) := by group
      _ = d * (r * (g⁻¹ * g⁻¹)) := by
          rw [show g⁻¹ * r = r * g⁻¹ from (hgr.inv_left).eq.symm.symm ▸ (hgr.inv_left).eq]
          group
      _ = d * (r * (g * g)⁻¹) := by rw [mul_inv_rev]
      _ = d * (r * (r ^ k * r)⁻¹) := by rw [hg2]
      _ = d * (r ^ k)⁻¹ := by
          rw [mul_inv_rev]
          group
      _ = d * r ^ k := by rw [hzi]
      _ = r ^ k * d := hdz
  exact hmain.symm

theorem dihedral_center_mul_conj_even (hd : d * d = 1) (he : e * e = 1) {j : ℕ} (hev : Even j) :
    (d * e) ^ j * d = (d * e) ^ (j / 2) * d * ((d * e) ^ (j / 2))⁻¹ := by
  obtain ⟨c, hc⟩ := hev
  have hj : j / 2 = c := by omega
  rw [hj, hc]
  have h := dihedral_conj_pow hd he c
  have hrd : (d * e) ^ c * d = d * ((d * e) ^ c)⁻¹ := by
    calc (d * e) ^ c * d = (d * d) * (d * e) ^ c * d := by rw [hd, one_mul]
      _ = d * (d * (d * e) ^ c * d) := by group
      _ = d * ((d * e) ^ c)⁻¹ := by rw [h]
  calc (d * e) ^ (c + c) * d = (d * e) ^ c * ((d * e) ^ c * d) := by rw [pow_add, mul_assoc]
    _ = (d * e) ^ c * (d * ((d * e) ^ c)⁻¹) := by rw [hrd]
    _ = (d * e) ^ c * d * ((d * e) ^ c)⁻¹ := by group

theorem dihedral_center_mul_mem {S : Set G} (hS : ∀ g x, x ∈ S → g * x * g⁻¹ ∈ S)
    (hd : d * d = 1) (he : e * e = 1) {j : ℕ} (hr : (d * e) ^ (2 * j) = 1) (hdS : d ∈ S)
    (heS : e ∈ S) : (d * e) ^ j * d ∈ S ∧ (d * e) ^ j * e ∈ S := by
  have hz2 : (d * e) ^ j * (d * e) ^ j = 1 := by rw [← pow_add, ← two_mul]; exact hr
  have hz' : (e * d) ^ j = (d * e) ^ j := by
    rw [← dihedral_inv hd he, inv_pow]
    exact inv_eq_of_mul_eq_one_right hz2
  have hr' : (e * d) ^ (2 * j) = 1 := by
    rw [← dihedral_inv hd he, inv_pow, hr, inv_one]
  rcases Nat.even_or_odd j with hev | hod
  · refine ⟨?_, ?_⟩
    · rw [dihedral_center_mul_conj_even hd he hev]
      exact hS _ _ hdS
    · have h := dihedral_center_mul_conj_even he hd hev (j := j)
      rw [hz'] at h
      rw [h]
      exact hS _ _ heS
  · refine ⟨?_, ?_⟩
    · rw [dihedral_center_mul_conj hd he hod hr]
      exact hS _ _ heS
    · have h := dihedral_center_mul_conj he hd hod hr'
      rw [hz'] at h
      rw [h]
      exact hS _ _ hdS

theorem dihedral_inv_pow_conj (hd : d * d = 1) (he : e * e = 1) (i : ℕ) :
    d * ((d * e) ^ i)⁻¹ * d = (d * e) ^ i := by
  have h := dihedral_conj_pow hd he i
  have h2 := congrArg (fun x => x⁻¹) h
  simp only [inv_inv] at h2
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [mul_inv_rev, mul_inv_rev, hdi] at h2
  rw [mul_assoc]
  exact h2

theorem dihedral_mul_conj_inv_pow (hd : d * d = 1) (he : e * e = 1) (i : ℕ) :
    d * (((d * e) ^ i)⁻¹ * d * (d * e) ^ i) = (d * e) ^ i * (d * e) ^ i := by
  have h := dihedral_inv_pow_conj hd he i
  calc d * (((d * e) ^ i)⁻¹ * d * (d * e) ^ i)
      = (d * ((d * e) ^ i)⁻¹ * d) * (d * e) ^ i := by group
    _ = (d * e) ^ i * (d * e) ^ i := by rw [h]

theorem dihedral_mul_conj_inv_pow' (hd : d * d = 1) (he : e * e = 1) (i : ℕ) :
    d * (((d * e) ^ i)⁻¹ * e * (d * e) ^ i) = (d * e) ^ (2 * i + 1) := by
  have h := dihedral_inv_pow_conj hd he i
  have hee : e = d * (d * e) := by
    calc e = (d * d) * e := by rw [hd, one_mul]
      _ = d * (d * e) := by group
  calc d * (((d * e) ^ i)⁻¹ * e * (d * e) ^ i)
      = d * (((d * e) ^ i)⁻¹ * (d * (d * e)) * (d * e) ^ i) := by rw [← hee]
    _ = (d * ((d * e) ^ i)⁻¹ * d) * (d * e) * (d * e) ^ i := by group
    _ = (d * e) ^ i * (d * e) * (d * e) ^ i := by rw [h]
    _ = (d * e) ^ (2 * i + 1) := by
      rw [show 2 * i + 1 = i + 1 + i by omega, pow_add, pow_succ]

end CFSG.CGT.Timmesfeld75
