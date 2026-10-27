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

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.QSub

open QuaternionGroup
open scoped commutatorElement

namespace Alg

section General

variable {n : ℕ} [NeZero n]

theorem n_ne_zero : ((n : ℕ) : ZMod (2 * n)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 := Nat.le_of_dvd (NeZero.pos n) h
  have h2 := NeZero.pos n
  omega

omit [NeZero n] in
theorem n_add_n : ((n : ℕ) : ZMod (2 * n)) + ((n : ℕ) : ZMod (2 * n)) = 0 := by
  have h := ZMod.natCast_self (2 * n)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [← two_mul]
  exact h

theorem two_mul_eq_zero_iff {x : ZMod (2 * n)} :
    2 * x = 0 ↔ x = 0 ∨ x = ((n : ℕ) : ZMod (2 * n)) := by
  constructor
  · intro h
    have h1 : ((2 * x.val : ℕ) : ZMod (2 * n)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat]
      exact h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : n ∣ x.val := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h1
    obtain ⟨k, hk⟩ := h2
    have h3 := ZMod.val_lt x
    have hk2 : k < 2 := by
      by_contra hk2
      have hk3 : 2 ≤ k := by omega
      have : n * 2 ≤ n * k := Nat.mul_le_mul_left n hk3
      omega
    interval_cases k
    · left
      rw [← ZMod.natCast_zmod_val x, hk]
      simp
    · right
      rw [← ZMod.natCast_zmod_val x, hk]
      simp
  · rintro (rfl | rfl)
    · simp
    · rw [two_mul ((n : ℕ) : ZMod (2 * n))]
      exact n_add_n

end General

section QuatGeneral

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem inv_a (i : ZMod (2 * n)) : (a i : QuaternionGroup n)⁻¹ = a (-i) :=
  inv_eq_of_mul_eq_one_right (by rw [a_mul_a, add_neg_cancel, a_zero])

omit [NeZero n] in
theorem inv_xa (i : ZMod (2 * n)) :
    (xa i : QuaternionGroup n)⁻¹ = xa (((n : ℕ) : ZMod (2 * n)) + i) :=
  inv_eq_of_mul_eq_one_right (by
    rw [xa_mul_xa, show ((n : ℕ) : ZMod (2 * n)) + (((n : ℕ) : ZMod (2 * n)) + i) - i =
      ((n : ℕ) : ZMod (2 * n)) + ((n : ℕ) : ZMod (2 * n)) by ring, n_add_n, a_zero])

omit [NeZero n] in
theorem a_pow (i : ZMod (2 * n)) (k : ℕ) :
    (a i : QuaternionGroup n) ^ k = a ((k : ZMod (2 * n)) * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem a_eq_pow (i : ZMod (2 * n)) : (a i : QuaternionGroup n) = (a 1) ^ i.val := by
  rw [a_one_pow, ZMod.natCast_zmod_val]

theorem mem_zpowers_a_one_iff (x : QuaternionGroup n) :
    x ∈ Subgroup.zpowers (a 1 : QuaternionGroup n) ↔ ∃ i, x = a i := by
  constructor
  · intro hx
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [← hk, a_one_pow]⟩
  · rintro ⟨i, rfl⟩
    rw [a_eq_pow i]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit [NeZero n] in
theorem a_n_mul_self :
    (a ((n : ℕ) : ZMod (2 * n)) : QuaternionGroup n) * a ((n : ℕ) : ZMod (2 * n)) = 1 := by
  rw [a_mul_a, n_add_n, a_zero]

theorem a_n_ne_one : (a ((n : ℕ) : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := fun h =>
  n_ne_zero (a.inj (h.trans a_zero.symm))

theorem eq_of_mul_self_eq_one_aux (p : QuaternionGroup n) (hp : p * p = 1) :
    p = 1 ∨ p = a ((n : ℕ) : ZMod (2 * n)) := by
  rcases p with i | i
  · rw [a_mul_a, ← a_zero] at hp
    have h := a.inj hp
    rw [← two_mul] at h
    rcases two_mul_eq_zero_iff.mp h with h | h
    · left
      rw [h, a_zero]
    · right
      rw [h]
  · exfalso
    rw [xa_mul_xa, add_sub_cancel_right, ← a_zero] at hp
    exact n_ne_zero (a.inj hp)

omit [NeZero n] in
theorem commutator_a_xa (k : ZMod (2 * n)) :
    ⁅(a k : QuaternionGroup n), xa 0⁆ = a (k + k) := by
  rw [commutatorElement_def, inv_a, inv_xa, a_mul_xa, xa_mul_a, xa_mul_xa]
  congr 1
  linear_combination (n_add_n (n := n))

theorem orderOf_eq_four_of_mul_self {G : Type*} [Group G] {y z : G} (h : y * y = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : orderOf y = 4 := by
  have h1 : ¬ y ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, h]
    exact hz1
  have h2 : y ^ 2 ^ (1 + 1) = 1 := by
    have e4 : y ^ 2 ^ (1 + 1) = (y * y) * (y * y) := by
      rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e4, h, hz2]
  rw [orderOf_eq_prime_pow h1 h2]
  norm_num

end QuatGeneral

theorem exists_half {m : ℕ} (hm : 1 ≤ m) :
    ∃ k : ZMod (2 * 2 ^ m), k + k = ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  refine ⟨((2 ^ j : ℕ) : ZMod (2 * 2 ^ (j + 1))), ?_⟩
  rw [← Nat.cast_add, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by ring]

theorem nn_eq (m : ℕ) :
    ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m)) = (2 : ZMod (2 * 2 ^ m)) ^ m := by
  simp

section Transport

variable {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ}
  (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

theorem coe_symm_mul (x y : QuaternionGroup (2 ^ (r - 2))) :
    ((e.symm x : ↥Q) : G) * ((e.symm y : ↥Q) : G) = ((e.symm (x * y) : ↥Q) : G) := by
  rw [map_mul, Subgroup.coe_mul]

theorem coe_symm_inv (x : QuaternionGroup (2 ^ (r - 2))) :
    ((e.symm x : ↥Q) : G)⁻¹ = ((e.symm x⁻¹ : ↥Q) : G) := by
  rw [map_inv, Subgroup.coe_inv]

theorem coe_symm_one : ((e.symm 1 : ↥Q) : G) = 1 := by
  rw [map_one, Subgroup.coe_one]

theorem coe_symm_inj {x y : QuaternionGroup (2 ^ (r - 2))} :
    ((e.symm x : ↥Q) : G) = ((e.symm y : ↥Q) : G) ↔ x = y :=
  ⟨fun h => e.symm.injective (Subtype.ext h), fun h => h ▸ rfl⟩

theorem exists_coe_symm {p : G} (hp : p ∈ Q) :
    ∃ x : QuaternionGroup (2 ^ (r - 2)), p = ((e.symm x : ↥Q) : G) :=
  ⟨e ⟨p, hp⟩, by rw [MulEquiv.symm_apply_apply]⟩

theorem orderOf_coe_symm (x : QuaternionGroup (2 ^ (r - 2))) :
    orderOf ((e.symm x : ↥Q) : G) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem z_eq :
    ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) =
      ((e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) : ↥Q) : G) := by
  rw [nn_eq]

theorem z_mul_self :
    ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) *
      ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) = 1 := by
  rw [z_eq, coe_symm_mul, a_n_mul_self, coe_symm_one]

theorem z_ne_one : ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) ≠ 1 := by
  rw [z_eq, ← coe_symm_one e, Ne, coe_symm_inj]
  exact a_n_ne_one

end Transport

end Alg

section Main

open Alg

variable {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ}
  (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

@[expose] def xc : Subgroup G :=
  (Subgroup.zpowers (e.symm (QuaternionGroup.a 1))).map Q.subtype

theorem mem_xc_iff {y : G} :
    y ∈ xc e ↔ ∃ i : ZMod (2 * 2 ^ (r - 2)),
      y = ((e.symm (QuaternionGroup.a i) : ↥Q) : G) := by
  unfold xc
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : e x ∈ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) := by
      have := Subgroup.mem_map_of_mem e.toMonoidHom hx
      rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
    obtain ⟨i, hi⟩ := (mem_zpowers_a_one_iff _).mp h1
    refine ⟨i, ?_⟩
    rw [← hi, MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨i, rfl⟩
    refine ⟨e.symm (QuaternionGroup.a i), ?_, rfl⟩
    have h1 : (QuaternionGroup.a i : QuaternionGroup (2 ^ (r - 2))) ∈
        Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (r - 2))) :=
      (mem_zpowers_a_one_iff _).mpr ⟨i, rfl⟩
    have := Subgroup.mem_map_of_mem e.symm.toMonoidHom h1
    rwa [MonoidHom.map_zpowers] at this

theorem xc_le : xc e ≤ Q := by
  intro y hy
  obtain ⟨i, rfl⟩ := (mem_xc_iff e).mp hy
  exact (e.symm _).2

theorem eq_of_mul_self_eq_one {y : G} (hy : y ∈ Q) (h : y * y = 1) :
    y = 1 ∨ y = ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) := by
  obtain ⟨x, rfl⟩ := exists_coe_symm e hy
  rw [coe_symm_mul, ← coe_symm_one e, coe_symm_inj] at h
  rw [z_eq, ← coe_symm_one e, coe_symm_inj, coe_symm_inj]
  exact eq_of_mul_self_eq_one_aux x h

theorem eq_xc_of_cyclic_index_two (hr : 4 ≤ r) {U : Subgroup G} (hUQ : U ≤ Q)
    (hc : IsCyclic ↥U) (hi : U.relIndex Q = 2) : U = xc e := by
  have hn4 : 4 ≤ 2 ^ (r - 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Finite ↥Q := Finite.of_equiv _ e.symm.toEquiv
  have hcardQ : Nat.card ↥Q = 4 * 2 ^ (r - 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hU : 2 * Nat.card ↥U = Nat.card ↥Q := by
    have h := Subgroup.relIndex_mul_card U Q
    rwa [hi, inf_of_le_left hUQ] at h
  have := hc
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := ↥U)
  have hord : orderOf u₀ = Nat.card ↥U := orderOf_eq_card_of_forall_mem_zpowers hu₀
  have huQ : (u₀ : G) ∈ Q := hUQ u₀.2
  obtain ⟨x, hx⟩ := exists_coe_symm e huQ
  have hordx : orderOf x = 2 * 2 ^ (r - 2) := by
    rw [← orderOf_coe_symm e x, ← hx, Subgroup.orderOf_coe, hord]
    omega
  obtain ⟨i, rfl⟩ : ∃ i, x = QuaternionGroup.a i := by
    rcases x with i | j
    · exact ⟨i, rfl⟩
    · exfalso
      rw [QuaternionGroup.orderOf_xa] at hordx
      omega
  have huX : (u₀ : G) ∈ xc e := (mem_xc_iff e).mpr ⟨i, hx⟩
  have hle : U ≤ xc e := by
    intro w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hu₀ ⟨w, hw⟩)
    have hwu : w = (u₀ : G) ^ k := by
      have h1 := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at h1
      exact h1.symm
    rw [hwu]
    exact (xc e).zpow_mem huX k
  have : Finite ↥(xc e) :=
    Finite.of_injective (Subgroup.inclusion (xc_le e)) (Subgroup.inclusion_injective _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hXcard : Nat.card ↥(xc e) = 2 * 2 ^ (r - 2) := by
    unfold xc
    rw [Subgroup.card_map_of_injective Q.subtype_injective, Nat.card_zpowers,
      MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  omega

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.QSub
