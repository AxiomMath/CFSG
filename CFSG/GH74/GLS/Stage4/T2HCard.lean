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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

public section

namespace CFSG.GH74.GLS.Stage4.Rest

section Card

variable {G : Type} [Group G]

theorem t2H_card_sup_comm_disjoint [Finite G] (P Q : Subgroup G)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hd : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  have hcomm : ∀ (m : ↥P) (n : ↥Q), Commute (P.subtype m) (Q.subtype n) :=
    fun m n => (hc m m.2 n n.2 : (m : G) * n = n * m)
  have hinj : Function.Injective (MonoidHom.noncommCoprod P.subtype Q.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod P.subtype Q.subtype hcomm).range = P ⊔ Q := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(P ⊔ Q) = Nat.card ↥(MonoidHom.noncommCoprod P.subtype Q.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥P × ↥Q) := (Nat.card_range_of_injective hinj)
    _ = Nat.card ↥P * Nat.card ↥Q := Nat.card_prod _ _

end Card

section Cyc

variable {G : Type} [Group G]

theorem t2H_zpow_invol {w : G} (hw : w * w = 1) (r : ℤ) : w ^ r = 1 ∨ w ^ r = w := by
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  rcases Int.even_or_odd' r with ⟨s, hs | hs⟩
  · left; rw [hs, zpow_mul, hw2, one_zpow]
  · right; rw [hs, zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]

theorem t2H_cyclic_even_part (H : Subgroup G) (hH : IsCyclic ↥H) (k : ℕ) (hk : Odd k)
    (hcard : Nat.card ↥H = 2 * k) (z : G) (hzH : z ∈ H) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ Q : Subgroup G, Q ≤ H ∧ Nat.card ↥Q = k ∧ (∀ x ∈ Q, Odd (orderOf x)) ∧
      (∀ x ∈ H, ∃ a ∈ Subgroup.zpowers z, ∃ b ∈ Q, x = a * b) ∧
      Subgroup.zpowers z ⊓ Q = ⊥ := by
  obtain ⟨g, hg⟩ := hH.exists_generator
  set c : G := (g : G) with hc
  have hord : orderOf c = 2 * k := by
    rw [hc, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hcard
  have hpow : ∀ x ∈ H, ∃ n : ℤ, c ^ n = x := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact ⟨n, congrArg Subtype.val hn⟩
  have hcH : c ∈ H := g.2
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2' hz1
  have hck : (c ^ k) * (c ^ k) = 1 := by
    rw [← pow_add, ← two_mul, ← hord]; exact pow_orderOf_eq_one c
  have hzc : z = c ^ k := by
    obtain ⟨m, hm⟩ := hpow z hzH
    have h1 : c ^ (m + m) = 1 := by rw [zpow_add, hm, hz2]
    have h2 : ((2 * k : ℕ) : ℤ) ∣ m + m := by
      rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have h3 : (k : ℤ) ∣ m := by
      have : (2 : ℤ) * k ∣ 2 * m := by
        have e : m + m = 2 * m := by ring
        rw [e] at h2; simpa using h2
      exact Int.dvd_of_mul_dvd_mul_left (by norm_num) this
    obtain ⟨r, hr⟩ := h3
    have h4 : z = (c ^ k) ^ r := by
      rw [← hm, hr, zpow_mul]; simp
    rcases t2H_zpow_invol hck r with h5 | h5
    · exfalso; apply hz1; rw [h4, h5]
    · rw [h4, h5]
  refine ⟨Subgroup.zpowers (c ^ 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.2 (H.pow_mem hcH 2)
  · rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hord]; exact dvd_mul_right 2 k),
      hord]
    omega
  · intro x hx
    have := orderOf_dvd_of_mem_zpowers hx
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; exact dvd_mul_right 2 k), hord] at this
    exact Odd.of_dvd_nat hk (by simpa using this)
  · intro x hx
    obtain ⟨n, rfl⟩ := hpow x hx
    obtain ⟨j, hj⟩ := hk
    refine ⟨z ^ n, Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) n,
      (c ^ 2) ^ (-(j * n : ℤ)), Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _, ?_⟩
    have hz' : z = c ^ (k : ℤ) := by rw [hzc, zpow_natCast]
    have hc2 : c ^ 2 = c ^ (2 : ℤ) := by rw [pow_two, zpow_two]
    calc c ^ n = c ^ ((k : ℤ) * n + 2 * (-((j : ℤ) * n))) := by
          congr 1; rw [hj]; push_cast; ring
      _ = c ^ ((k : ℤ) * n) * c ^ (2 * (-((j : ℤ) * n))) := zpow_add _ _ _
      _ = (c ^ (k : ℤ)) ^ n * (c ^ (2 : ℤ)) ^ (-((j : ℤ) * n)) := by rw [zpow_mul, zpow_mul]
      _ = z ^ n * (c ^ 2) ^ (-((j : ℤ) * n)) := by rw [← hz', hc2]
  · rw [eq_bot_iff]
    intro x ⟨hxz, hxQ⟩
    have h1 := orderOf_dvd_of_mem_zpowers hxz
    have h2 := orderOf_dvd_of_mem_zpowers hxQ
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; exact dvd_mul_right 2 k), hord,
      Nat.mul_div_cancel_left _ (by norm_num)] at h2
    rw [hzo] at h1
    have h3 : orderOf x ∣ Nat.gcd 2 k := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 k = 1 := by
      obtain ⟨j, hj⟩ := hk
      rw [hj]; simp [Nat.gcd_comm]
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3

end Cyc

end CFSG.GH74.GLS.Stage4.Rest
