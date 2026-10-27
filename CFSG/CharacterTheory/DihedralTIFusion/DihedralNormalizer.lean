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

namespace CFSG.DihedralTIFusion

variable {G : Type*} [Group G] {W : Subgroup G} {u : G}

theorem eq_one_of_mul_self_eq_one_of_odd (hWodd : Odd (Nat.card W)) {w : G} (hw : w ∈ W)
    (hww : w * w = 1) : w = 1 := by
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
  have hW : orderOf w ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hw
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hW
    exact absurd (even_iff_two_dvd.mpr hW) (Nat.not_even_iff_odd.mpr hWodd)

theorem exists_mul_self_eq_of_odd (hWodd : Odd (Nat.card W)) {w : G} (hw : w ∈ W) :
    ∃ v ∈ W, v * v = w := by
  obtain ⟨k, hk⟩ := hWodd
  refine ⟨w ^ (k + 1), W.pow_mem hw _, ?_⟩
  have hpow : w ^ Nat.card W = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard W hw)
  rw [← pow_add, show k + 1 + (k + 1) = Nat.card W + 1 by omega, pow_succ, hpow, one_mul]

theorem conj_eq_inv_of_inverts (hu2 : u * u = 1) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    {w : G} (hw : w ∈ W) : u * w * u = w⁻¹ := by
  rw [← hinvert w hw, inv_eq_of_mul_eq_one_right hu2]

theorem mem_sup_zpowers_iff (hu2 : u * u = 1) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹)
    (g : G) : g ∈ W ⊔ Subgroup.zpowers u ↔ g ∈ W ∨ g * u ∈ W := by
  let H : Subgroup G :=
    { carrier := {g | g ∈ W ∨ g * u ∈ W}
      one_mem' := Or.inl W.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (W.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact W.mul_mem ha hb)
        · refine Or.inr ?_
          have h : a * b * u = (a * u) * (u⁻¹ * b * u) := by group
          rw [h, hinvert b hb]
          exact W.mul_mem ha (W.inv_mem hb)
        · refine Or.inl ?_
          have h : a * b = (a * u) * (u⁻¹ * (b * u) * u) := by
            calc a * b = a * b * (u * u) := by rw [hu2, mul_one]
              _ = (a * u) * (u⁻¹ * (b * u) * u) := by group
          rw [h, hinvert _ hb]
          exact W.mul_mem ha (W.inv_mem hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (W.inv_mem ha)
        · refine Or.inr ?_
          have h : a⁻¹ * u = u⁻¹ * (a * u)⁻¹ * u := by
            calc a⁻¹ * u = (u * u)⁻¹ * a⁻¹ * u := by rw [hu2, inv_one, one_mul]
              _ = u⁻¹ * (a * u)⁻¹ * u := by group
          rw [h, hinvert _ (W.inv_mem ha), inv_inv]
          exact ha }
  have hle : W ⊔ Subgroup.zpowers u ≤ H := sup_le (fun w hw => Or.inl hw)
    (Subgroup.zpowers_le.mpr (Or.inr (by rw [hu2]; exact W.one_mem)))
  refine ⟨fun hg => hle hg, ?_⟩
  rintro (hg | hg)
  · exact Subgroup.mem_sup_left hg
  · have h : g = (g * u) * u⁻¹ := by group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers u)))

theorem inv_conj_eq_inv_of_mul_mem (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hu2 : u * u = 1) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹) {n : G} (hn : n * u ∈ W)
    {w : G} (hw : w ∈ W) : n⁻¹ * w * n = w⁻¹ := by
  have h1 : (n * u)⁻¹ * w * (n * u) = w := by
    rw [mul_assoc, hWcomm w hw _ hn, ← mul_assoc, inv_mul_cancel, one_mul]
  calc n⁻¹ * w * n = (u * u)⁻¹ * n⁻¹ * w * n * (u * u) := by rw [hu2]; group
    _ = u⁻¹ * ((n * u)⁻¹ * w * (n * u)) * u := by group
    _ = w⁻¹ := by rw [h1, hinvert w hw]

theorem inv_mul_conj_eq (hu2 : u * u = 1) (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹) {d : G}
    (hd : d ∈ W) : d⁻¹ * u * d = u * (d * d) := by
  have h := conj_eq_inv_of_inverts hu2 hinvert (W.inv_mem hd)
  rw [inv_inv] at h
  calc d⁻¹ * u * d = (u * u) * d⁻¹ * u * d := by rw [hu2, one_mul]
    _ = u * (u * d⁻¹ * u) * d := by group
    _ = u * (d * d) := by rw [h, mul_assoc]

theorem exists_conj_eq_of_mul_mem (hWodd : Odd (Nat.card W)) (hu2 : u * u = 1)
    (hinvert : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹) {n : G} (hn : n * u ∈ W) :
    ∃ d ∈ W, d⁻¹ * u * d = n := by
  have hc : u * (n * u) * u ∈ W := by
    rw [conj_eq_inv_of_inverts hu2 hinvert hn]
    exact W.inv_mem hn
  obtain ⟨d, hd, hdd⟩ := exists_mul_self_eq_of_odd hWodd hc
  refine ⟨d, hd, ?_⟩
  rw [inv_mul_conj_eq hu2 hinvert hd, hdd]
  calc u * (u * (n * u) * u) = (u * u) * n * (u * u) := by group
    _ = n := by rw [hu2, one_mul, mul_one]

end CFSG.DihedralTIFusion
