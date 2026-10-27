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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv

@[expose] def alt6c1 : Perm (Fin 6) := swap 0 1 * swap 0 2
@[expose] def alt6c2 : Perm (Fin 6) := swap 3 4 * swap 3 5
@[expose] def alt6t0 : Perm (Fin 6) := swap 0 1 * swap 3 4
@[expose] def alt6u0 : Perm (Fin 6) := swap 0 1 * swap 2 3
@[expose] def alt6s45 : Perm (Fin 6) := swap 4 5

theorem alt6c1_pow : alt6c1 ^ 3 = 1 := by decide
theorem alt6c2_pow : alt6c2 ^ 3 = 1 := by decide
theorem alt6c1_comm : alt6c1 * alt6c2 = alt6c2 * alt6c1 := by decide
theorem alt6t0_sq : alt6t0 * alt6t0 = 1 := by decide
theorem alt6t0_c1 : alt6t0 * alt6c1 = alt6c1 ^ 2 * alt6t0 := by decide
theorem alt6t0_c2 : alt6t0 * alt6c2 = alt6c2 ^ 2 * alt6t0 := by decide
theorem sign_alt6c1 : Perm.sign alt6c1 = 1 := by decide
theorem sign_alt6c2 : Perm.sign alt6c2 = 1 := by decide
theorem sign_alt6t0 : Perm.sign alt6t0 = 1 := by decide
theorem sign_alt6s45 : Perm.sign alt6s45 = -1 := by decide
theorem alt6s45_u0 : alt6s45 * alt6u0 * alt6s45⁻¹ = alt6u0 := by decide
theorem alt6c1_ne_one : alt6c1 ≠ 1 := by decide
theorem alt6t0_ne_one : alt6t0 ≠ 1 := by decide

theorem cycleType_alt6c1 : alt6c1.cycleType = {3} :=
  (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem cycleType_alt6c2 : alt6c2.cycleType = {3} :=
  (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem alt6_disjoint : Perm.Disjoint alt6c1 alt6c2 := by
  intro x; fin_cases x <;> decide

theorem cycleType_alt6c12 : (alt6c1 * alt6c2).cycleType = {3, 3} := by
  rw [Perm.Disjoint.cycleType_mul alt6_disjoint, cycleType_alt6c1, cycleType_alt6c2]
  rfl

theorem cycleType_alt6u0 : alt6u0.cycleType = {2, 2} := by
  have hd : Perm.Disjoint (swap (0 : Fin 6) 1) (swap 2 3) := by
    intro x; fin_cases x <;> decide
  have h1 : (swap (0 : Fin 6) 1).cycleType = {2} := by
    rw [(Perm.isCycle_swap (by decide)).cycleType, Perm.card_support_swap (by decide)]
  have h2 : (swap (2 : Fin 6) 3).cycleType = {2} := by
    rw [(Perm.isCycle_swap (by decide)).cycleType, Perm.card_support_swap (by decide)]
  rw [alt6u0, Perm.Disjoint.cycleType_mul hd, h1, h2]
  rfl

theorem cycleType_of_orderOf_three_perm6 {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  have hall : ∀ m ∈ σ.cycleType, m = 3 := by
    intro m hm
    have h1 : m ∣ 3 := h ▸ Perm.dvd_of_mem_cycleType hm
    have h2 : 2 ≤ m := Perm.two_le_of_mem_cycleType hm
    have := Nat.le_of_dvd (by norm_num) h1
    interval_cases m
    · omega
    · rfl
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Perm.sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin 6) := Finset.card_le_univ _
      _ = 6 := by simp
  have hk : Multiset.card σ.cycleType ≤ 2 := by
    have : σ.cycleType.sum = 3 * Multiset.card σ.cycleType := by
      conv_lhs => rw [hrep]
      simp [Multiset.sum_replicate, mul_comm]
    omega
  have hk0 : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have : σ.cycleType = 0 := Multiset.card_eq_zero.mp h0
    have h1 : σ = 1 := Perm.cycleType_eq_zero.mp this
    rw [h1, orderOf_one] at h
    omega
  rw [hrep]
  interval_cases hc : Multiset.card σ.cycleType
  · omega
  · left; rfl
  · right; rfl

theorem perm6_order3 {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    ∃ π : Perm (Fin 6), π * alt6c1 * π⁻¹ = σ ∨ π * (alt6c1 * alt6c2) * π⁻¹ = σ := by
  rcases cycleType_of_orderOf_three_perm6 h with h1 | h1
  · have : IsConj alt6c1 σ := Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_alt6c1, h1])
    obtain ⟨π, hπ⟩ := isConj_iff.mp this
    exact ⟨π, Or.inl hπ⟩
  · have : IsConj (alt6c1 * alt6c2) σ :=
      Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_alt6c12, h1])
    obtain ⟨π, hπ⟩ := isConj_iff.mp this
    exact ⟨π, Or.inr hπ⟩

theorem cycleType_of_involution_perm6 {σ : Perm (Fin 6)} (h : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : Perm.sign σ = 1) : σ.cycleType = {2, 2} := by
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have hall : ∀ m ∈ σ.cycleType, m = 2 := by
    intro m hm
    have h1 : m ∣ 2 := (Perm.dvd_of_mem_cycleType hm).trans hord
    have h2 : 2 ≤ m := Perm.two_le_of_mem_cycleType hm
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Perm.sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin 6) := Finset.card_le_univ _
      _ = 6 := by simp
  have hsum' : σ.cycleType.sum = 2 * Multiset.card σ.cycleType := by
    conv_lhs => rw [hrep]
    simp [Multiset.sum_replicate, mul_comm]
  have hk : Multiset.card σ.cycleType ≤ 3 := by omega
  have hk0 : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have : σ.cycleType = 0 := Multiset.card_eq_zero.mp h0
    exact h1 (Perm.cycleType_eq_zero.mp this)
  have hsign := Perm.sign_of_cycleType σ
  rw [hs, hsum'] at hsign
  rw [hrep]
  interval_cases hc : Multiset.card σ.cycleType
  · omega
  · norm_num at hsign
  · rfl
  · norm_num at hsign

theorem perm6_involution_conj {u : Perm (Fin 6)} (hu : u * u = 1) (hu1 : u ≠ 1)
    (hs : Perm.sign u = 1) : ∃ π : Perm (Fin 6), Perm.sign π = 1 ∧ π * alt6u0 * π⁻¹ = u := by
  have : IsConj alt6u0 u := Perm.isConj_iff_cycleType_eq.mpr
    (by rw [cycleType_alt6u0, cycleType_of_involution_perm6 hu hu1 hs])
  obtain ⟨π, hπ⟩ := isConj_iff.mp this
  by_cases hsp : Perm.sign π = 1
  · exact ⟨π, hsp, hπ⟩
  · have hneg : Perm.sign π = -1 := by
      rcases Int.units_eq_one_or (Perm.sign π) with h | h
      · exact absurd h hsp
      · exact h
    refine ⟨π * alt6s45, ?_, ?_⟩
    · rw [map_mul, hneg, sign_alt6s45]; rfl
    · calc π * alt6s45 * alt6u0 * (π * alt6s45)⁻¹
          = π * (alt6s45 * alt6u0 * alt6s45⁻¹) * π⁻¹ := by group
        _ = u := by rw [alt6s45_u0, hπ]

section Generic

variable {G : Type*} [Group G]

theorem mem_of_card_eq_four {J : Subgroup G} [Finite J] (hJ : Nat.card J = 4) {a b c d : G}
    (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hd : d ∈ J) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ∀ x ∈ J, x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  intro x hx
  by_contra hne
  push Not at hne
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hne
  have hsub : (({a, b, c, d, x} : Finset G) : Set G) ⊆ (J : Set G) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d, x} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hxd.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hcd, hxc.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hbc, hbd, hxb.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, hac, had, hxa.symm⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at this
  have h4 : (J : Set G).ncard = 4 := by rw [← hJ]; exact Nat.card_coe_set_eq _
  omega

theorem exists_ne_two_of_card_eq_four {J : Subgroup G} [Finite J] (hJ : Nat.card J = 4) (u : G) :
    ∃ v ∈ J, v ≠ 1 ∧ v ≠ u := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (J : Set G) ⊆ (({1, u} : Finset G) : Set G) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h1 : w = 1
    · exact Or.inl h1
    · exact Or.inr (hne w hw h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h4 : (J : Set G).ncard = 4 := by rw [← hJ]; exact Nat.card_coe_set_eq _
  have h2 : ({1, u} : Finset G).card ≤ 2 := Finset.card_le_two
  omega

theorem not_mem_zpowers_of_pow_three {a b : G} (ha : a ^ 3 = 1) (h1 : b ≠ 1) (h2 : b ≠ a)
    (h3 : b ≠ a ^ 2) : b ∉ Subgroup.zpowers a := by
  intro hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hk : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul]
    have : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
    rw [this, one_zpow, mul_one]
  have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hm with h | h | h
  · rw [hk, h] at h1; simp at h1
  · rw [hk, h] at h2; simp at h2
  · rw [hk, h] at h3; simp at h3

theorem nine_dvd_card_sup_zpowers [Finite G] {x y : G} (hxy : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hnot : x ∉ Subgroup.zpowers y) :
    9 ∣ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ z : G, z ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers z) := by
    intro z hz g
    refine ⟨1, ?_⟩
    obtain ⟨g, k, rfl⟩ := g
    apply Subtype.ext
    show ((z ^ k) ^ 3 : G) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz
    rw [Nat.cast_ofNat, this, one_zpow]
  have hxcent : x ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    (Subgroup.zpowers_le.mpr hxcent).trans (Subgroup.centralizer_le_normalizer _)
  have hF : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    (hpow x hx3).to_sup_of_normal_right' (hpow y hy3) hnorm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hF
  have hyc : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y := le_sup_right
  have hlt : Nat.card (Subgroup.zpowers y) < Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    by_contra hge
    push Not at hge
    have heq := Subgroup.eq_of_le_of_card_ge hle hge
    apply hnot
    have : x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
      (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers x)
    rwa [← heq] at this
  rw [hyc, hn] at hlt
  rw [hn]
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> omega
  exact (pow_dvd_pow 3 hn2)

end Generic

@[expose] def alt6k1 : Perm (Fin 6) := swap 0 2 * swap 1 3
@[expose] def alt6k2 : Perm (Fin 6) := swap 0 3 * swap 1 2
@[expose] def alt6k3 : Perm (Fin 6) := swap 0 1 * swap 4 5
@[expose] def alt6k4 : Perm (Fin 6) := swap 2 3 * swap 4 5
@[expose] def alt6b2 : Perm (Fin 6) := swap 2 4 * swap 3 5

theorem perm6_klein_centralizer : ∀ v : Perm (Fin 6), v * v = 1 → Perm.sign v = 1 → v ≠ 1 →
    v ≠ alt6u0 → v * alt6u0 = alt6u0 * v →
      v = alt6k1 ∨ v = alt6k2 ∨ v = alt6k3 ∨ v = alt6k4 := by
  decide +kernel

theorem alt6_klein_witness {v : Perm (Fin 6)}
    (hv : v = alt6k1 ∨ v = alt6k2 ∨ v = alt6k3 ∨ v = alt6k4) :
    ∃ b : Perm (Fin 6), Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ b ≠ alt6u0 ∧ b ≠ v ∧
      b ≠ alt6u0 * v ∧
      b * alt6u0 * b⁻¹ ∈ [1, alt6u0, v, alt6u0 * v] ∧ b * v * b⁻¹ ∈ [1, alt6u0, v, alt6u0 * v] ∧
      b * (alt6u0 * v) * b⁻¹ ∈ [1, alt6u0, v, alt6u0 * v] ∧
      (b * alt6u0 * b⁻¹ ≠ alt6u0 ∨ b * v * b⁻¹ ≠ v) := by
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨alt6k3, by decide +kernel⟩
  · exact ⟨alt6k3, by decide +kernel⟩
  · exact ⟨alt6b2, by decide +kernel⟩
  · exact ⟨alt6b2, by decide +kernel⟩

theorem sign_conj_perm6 (π f : Perm (Fin 6)) : Perm.sign (π * f * π⁻¹) = Perm.sign f := by
  rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign π) (Perm.sign f), mul_assoc, mul_inv_cancel,
    mul_one]

theorem alt6_klein {J : Subgroup (Perm (Fin 6))} (hJalt : ∀ x ∈ J, Perm.sign x = 1)
    (hJcard : Nat.card J = 4) (hJexp : ∀ x ∈ J, x * x = 1) :
    ∃ b : Perm (Fin 6), Perm.sign b = 1 ∧ b * b = 1 ∧ b ∉ J ∧ (∀ x ∈ J, b * x * b⁻¹ ∈ J) ∧
      ∃ x ∈ J, b * x * b⁻¹ ≠ x := by
  classical
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [hJcard]; norm_num)
  obtain ⟨u, hu, hu1, -⟩ := exists_ne_two_of_card_eq_four hJcard 1
  obtain ⟨v, hv, hv1, hvu⟩ := exists_ne_two_of_card_eq_four hJcard u
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    intro x hx y hy
    have h1 := hJexp (x * y) (J.mul_mem hx hy)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hJexp x hx)
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hJexp y hy)
    have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [mul_inv_rev, hxinv, hyinv] at h2
    exact h2
  obtain ⟨π, hπs, hπ⟩ := perm6_involution_conj (hJexp u hu) hu1 (hJalt u hu)
  have hsv := hJalt v hv
  set v' : Perm (Fin 6) := π⁻¹ * v * π with hv'
  have hvπ : v = π * v' * π⁻¹ := by rw [hv']; group
  have hv'sign : Perm.sign v' = 1 := by
    have := sign_conj_perm6 π⁻¹ v
    rw [inv_inv] at this
    rw [hv', this, hsv]
  have hv'sq : v' * v' = 1 := by
    have := hJexp v hv
    calc v' * v' = π⁻¹ * (v * v) * π := by rw [hv']; group
      _ = 1 := by rw [this]; group
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hv1
    rw [hvπ, h]; group
  have hv'u0 : v' ≠ alt6u0 := by
    intro h
    apply hvu
    rw [hvπ, h, ← hπ]
  have hv'c : v' * alt6u0 = alt6u0 * v' := by
    have h := hcomm v hv u hu
    have : π⁻¹ * (v * u) * π = π⁻¹ * (u * v) * π := by rw [h]
    calc v' * alt6u0 = π⁻¹ * (v * u) * π := by rw [hv', ← hπ]; group
      _ = π⁻¹ * (u * v) * π := this
      _ = alt6u0 * v' := by rw [hv', ← hπ]; group
  obtain ⟨b', hb's, hb'sq, hb'1, hb'u0, hb'v', hb'uv, hm1, hm2, hm3, hmove⟩ :=
    alt6_klein_witness (perm6_klein_centralizer v' hv'sq hv'sign hv'1 hv'u0 hv'c)
  have huv : u * v ∈ J := J.mul_mem hu hv
  have hJeq : ∀ x ∈ J, x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
    have had : (1 : Perm (Fin 6)) ≠ u * v := by
      intro h
      apply hvu
      have h' : v = u⁻¹ := eq_inv_of_mul_eq_one_right h.symm
      rw [h']
      exact inv_eq_of_mul_eq_one_right (hJexp u hu)
    have hbd : u ≠ u * v := by
      intro h
      apply hv1
      have := congrArg (fun w => u⁻¹ * w) h
      simpa using this.symm
    have hcd : v ≠ u * v := by
      intro h
      apply hu1
      have := congrArg (fun w => w * v⁻¹) h
      simpa using this.symm
    exact mem_of_card_eq_four hJcard J.one_mem hu hv huv hu1.symm hv1.symm had hvu.symm hbd hcd
  set b : Perm (Fin 6) := π * b' * π⁻¹ with hb
  have hcj : ∀ f g : Perm (Fin 6), π * f * π⁻¹ = π * g * π⁻¹ → f = g := by
    intro f g h
    have := congrArg (fun w => π⁻¹ * w * π) h
    simpa [mul_assoc] using this
  have hu' : u = π * alt6u0 * π⁻¹ := hπ.symm
  have huv' : u * v = π * (alt6u0 * v') * π⁻¹ := by rw [hu', hvπ]; group
  have h1' : (1 : Perm (Fin 6)) = π * 1 * π⁻¹ := by group
  have hbJ : b * u * b⁻¹ = π * (b' * alt6u0 * b'⁻¹) * π⁻¹ := by rw [hb, hu']; group
  have hbJ2 : b * v * b⁻¹ = π * (b' * v' * b'⁻¹) * π⁻¹ := by rw [hb, hvπ]; group
  have hbJ3 : b * (u * v) * b⁻¹ = π * (b' * (alt6u0 * v') * b'⁻¹) * π⁻¹ := by rw [hb, huv']; group
  have hmemJ : ∀ w : Perm (Fin 6), w ∈ [1, alt6u0, v', alt6u0 * v'] → π * w * π⁻¹ ∈ J := by
    intro w hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [← h1']; exact J.one_mem
    · rw [← hu']; exact hu
    · rw [← hvπ]; exact hv
    · rw [← huv']; exact huv
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, sign_conj_perm6, hb's]
  · calc b * b = π * (b' * b') * π⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hb'sq]; group
  · intro hbJ'
    rcases hJeq b hbJ' with h | h | h | h
    · apply hb'1; apply hcj; rw [← hb, h]; group
    · apply hb'u0; apply hcj; rw [← hb, h, hu']
    · apply hb'v'; apply hcj; rw [← hb, h, hvπ]
    · apply hb'uv; apply hcj; rw [← hb, h, huv']
  · intro x hx
    rcases hJeq x hx with rfl | rfl | rfl | rfl
    · have : b * (1 : Perm (Fin 6)) * b⁻¹ = 1 := by group
      rw [this]; exact J.one_mem
    · rw [hbJ]; exact hmemJ _ hm1
    · rw [hbJ2]; exact hmemJ _ hm2
    · rw [hbJ3]; exact hmemJ _ hm3
  · rcases hmove with h | h
    · refine ⟨u, hu, ?_⟩
      rw [hbJ]
      intro h'
      apply h
      apply hcj
      exact h'.trans hu'
    · refine ⟨v, hv, ?_⟩
      rw [hbJ2]
      intro h'
      apply h
      apply hcj
      exact h'.trans hvπ

section Abstract

variable {L : Type*} [Group L]

@[expose] def altSixEmb (e : L ≃* alternatingGroup (Fin 6)) : L →* Perm (Fin 6) :=
  (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom

theorem altSixEmb_injective (e : L ≃* alternatingGroup (Fin 6)) : Function.Injective (altSixEmb e) :=
  Subtype.val_injective.comp e.injective

theorem sign_altSixEmb (e : L ≃* alternatingGroup (Fin 6)) (x : L) :
    Perm.sign (altSixEmb e x) = 1 := by
  have := (e x).2
  rwa [Perm.mem_alternatingGroup] at this

theorem exists_altSixEmb_eq (e : L ≃* alternatingGroup (Fin 6)) {f : Perm (Fin 6)}
    (hf : Perm.sign f = 1) : ∃ x : L, altSixEmb e x = f :=
  ⟨e.symm ⟨f, Perm.mem_alternatingGroup.mpr hf⟩, by simp [altSixEmb]⟩

theorem alt6_klein_abs (e : L ≃* alternatingGroup (Fin 6)) {J : Subgroup L} (hJcard : Nat.card J = 4)
    (hJexp : ∀ x ∈ J, x * x = 1) :
    ∃ b : L, b * b = 1 ∧ b ∉ J ∧ (∀ x ∈ J, b * x * b⁻¹ ∈ J) ∧ ∃ x ∈ J, b * x * b⁻¹ ≠ x := by
  set φ := altSixEmb e with hφ
  have hinj := altSixEmb_injective e
  have hcard : Nat.card (J.map φ) = 4 := by
    rw [Subgroup.card_map_of_injective hinj, hJcard]
  obtain ⟨b₁, hb₁s, hb₁sq, hb₁J, hb₁N, ⟨x₁, hx₁, hx₁ne⟩⟩ := alt6_klein
    (J := J.map φ) (by rintro _ ⟨x, -, rfl⟩; exact sign_altSixEmb e x) hcard
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hJexp x hx, map_one])
  obtain ⟨b, hb⟩ := exists_altSixEmb_eq e hb₁s
  have hconj : ∀ y : L, φ (b * y * b⁻¹) = b₁ * φ y * b₁⁻¹ := by
    intro y; rw [map_mul, map_mul, map_inv, hb]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · apply hinj; rw [map_mul, hb, hb₁sq, map_one]
  · intro hbJ; exact hb₁J ⟨b, hbJ, hb⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hb₁N (φ x) ⟨x, hx, rfl⟩
    have : b * x * b⁻¹ = y := by apply hinj; rw [hconj, hyx]
    rw [this]; exact hy
  · obtain ⟨x, hx, rfl⟩ := hx₁
    refine ⟨x, hx, fun h => hx₁ne ?_⟩
    have h2 := hconj x
    rw [h] at h2
    exact h2.symm

theorem alt6_involution_conj_abs (e : L ≃* alternatingGroup (Fin 6)) {u v : L} (hu : u * u = 1)
    (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : ∃ g : L, g * u * g⁻¹ = v := by
  have hinj := altSixEmb_injective e
  have hne : ∀ w : L, w ≠ 1 → altSixEmb e w ≠ 1 := fun w hw h => hw (hinj (by rw [h, map_one]))
  obtain ⟨π₁, hs₁, hπ₁⟩ := perm6_involution_conj (u := altSixEmb e u)
    (by rw [← map_mul, hu, map_one]) (hne u hu1) (sign_altSixEmb e u)
  obtain ⟨π₂, hs₂, hπ₂⟩ := perm6_involution_conj (u := altSixEmb e v)
    (by rw [← map_mul, hv, map_one]) (hne v hv1) (sign_altSixEmb e v)
  have hsg : Perm.sign (π₂ * π₁⁻¹) = 1 := by rw [map_mul, map_inv, hs₁, hs₂]; rfl
  obtain ⟨g, hg⟩ := exists_altSixEmb_eq e hsg
  refine ⟨g, hinj ?_⟩
  rw [map_mul, map_mul, map_inv, hg, ← hπ₁, ← hπ₂]
  group

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem isSimpleGroup_of_alt6 (e : L ≃* alternatingGroup (Fin 6)) : IsSimpleGroup L := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  exact e.isSimpleGroup

theorem sup_zpowers_eq_top_of_card_sixty (e : L ≃* alternatingGroup (Fin 6)) {H : Subgroup L}
    (hH : Nat.card H = 60) {g : L} (hg : g ∉ H) : H ⊔ Subgroup.zpowers g = ⊤ := by
  have hfin : Finite L := Finite.of_equiv _ e.symm.toEquiv
  have hsimple : IsSimpleGroup L := isSimpleGroup_of_alt6 e
  have hL : Nat.card L = 360 := by rw [Nat.card_congr e.toEquiv, card_alt6]
  set M := H ⊔ Subgroup.zpowers g with hM
  by_contra hne
  have hHM : H ≤ M := le_sup_left
  have hdvd : 60 ∣ Nat.card M := hH ▸ Subgroup.card_dvd_of_le hHM
  have hgM : g ∈ M := (le_sup_right : Subgroup.zpowers g ≤ M) (Subgroup.mem_zpowers g)
  have hlt : Nat.card H < Nat.card M := by
    by_contra hge
    push Not at hge
    have := Subgroup.eq_of_le_of_card_ge hHM hge
    exact hg (this ▸ hgM)
  have hcM : Nat.card M * M.index = 360 := by
    rw [Subgroup.card_mul_index, hL]
  have hidx3 : M.index ≤ 3 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hH] at hlt
    have hk2 : 2 ≤ k := by omega
    rw [hk] at hcM
    nlinarith
  have hidx1 : M.index ≠ 1 := by
    intro h
    exact hne (Subgroup.index_eq_one.mp h)
  have hfi : M.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hd : M.normalCore.index ∣ Nat.factorial M.index :=
    Subgroup.index_normalCore_dvd_factorial_index (H := M)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
  · rw [h, Subgroup.index_bot, hL] at hd
    have h2 : Nat.factorial M.index ≤ 6 := by
      interval_cases hi : M.index
      · omega
      · decide
      · decide
      · decide
    have := Nat.le_of_dvd (Nat.factorial_pos _) hd
    omega
  · apply hne
    exact eq_top_iff.mpr (h ▸ Subgroup.normalCore_le M)

theorem alt6_e9_data (e : L ≃* alternatingGroup (Fin 6)) {y : L} (hy : orderOf y = 3) :
    ∃ b₁ b₂ t x : L, b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧ t * t = 1 ∧ t ≠ 1 ∧
      t * b₁ = b₁ ^ 2 * t ∧ t * b₂ = b₂ ^ 2 * t ∧
      y ∈ Subgroup.closure ({b₁, b₂} : Set L) ∧ x ∈ Subgroup.closure ({b₁, b₂} : Set L) ∧
      x ∉ Subgroup.zpowers y ∧ x * y = y * x ∧ x ^ 3 = 1 := by
  have hinj := altSixEmb_injective e
  have hyo : orderOf (altSixEmb e y) = 3 := by rw [orderOf_injective (altSixEmb e) hinj y, hy]
  obtain ⟨π, hπ⟩ := perm6_order3 hyo
  have hmem : ∀ f : Perm (Fin 6), Perm.sign f = 1 → ∃ z : L, altSixEmb e z = π * f * π⁻¹ :=
    fun f hf => exists_altSixEmb_eq e (by rw [sign_conj_perm6, hf])
  obtain ⟨b₁, hb₁⟩ := hmem alt6c1 sign_alt6c1
  obtain ⟨b₂, hb₂⟩ := hmem alt6c2 sign_alt6c2
  obtain ⟨t, ht⟩ := hmem alt6t0 sign_alt6t0
  have hcj : ∀ f g : Perm (Fin 6), π * f * π⁻¹ = π * g * π⁻¹ → f = g := by
    intro f g h
    have := congrArg (fun w => π⁻¹ * w * π) h
    simpa [mul_assoc] using this
  have hcm : ∀ f g : Perm (Fin 6), π * f * π⁻¹ * (π * g * π⁻¹) = π * (f * g) * π⁻¹ := by
    intro f g; group
  have r1 : b₁ ^ 3 = 1 := hinj (by rw [map_pow, hb₁, conj_pow, alt6c1_pow, map_one]; group)
  have r2 : b₂ ^ 3 = 1 := hinj (by rw [map_pow, hb₂, conj_pow, alt6c2_pow, map_one]; group)
  have r3 : b₁ * b₂ = b₂ * b₁ :=
    hinj (by rw [map_mul, map_mul, hb₁, hb₂, hcm, hcm, alt6c1_comm])
  have r4 : t * t = 1 := hinj (by rw [map_mul, ht, hcm, alt6t0_sq, map_one]; group)
  have r5 : t ≠ 1 := by
    intro h
    have : altSixEmb e t = 1 := by rw [h, map_one]
    rw [ht] at this
    apply alt6t0_ne_one
    apply hcj
    rw [this]; group
  have r6 : t * b₁ = b₁ ^ 2 * t := by
    apply hinj
    rw [map_mul, map_mul, map_pow, ht, hb₁, conj_pow, hcm, hcm, alt6t0_c1]
  have r7 : t * b₂ = b₂ ^ 2 * t := by
    apply hinj
    rw [map_mul, map_mul, map_pow, ht, hb₂, conj_pow, hcm, hcm, alt6t0_c2]
  have hb₁1 : b₁ ≠ 1 := by
    intro h; have : altSixEmb e b₁ = 1 := by rw [h, map_one]
    rw [hb₁] at this
    apply alt6c1_ne_one; apply hcj; rw [this]; group
  have hb₂1 : b₂ ≠ 1 := by
    intro h; have : altSixEmb e b₂ = 1 := by rw [h, map_one]
    rw [hb₂] at this
    have : alt6c2 = 1 := by apply hcj; rw [this]; group
    revert this; decide
  have hc₂₁ : b₂ ≠ b₁ := by
    intro h
    have : altSixEmb e b₂ = altSixEmb e b₁ := by rw [h]
    rw [hb₁, hb₂] at this
    have := hcj _ _ this
    revert this; decide
  have hc₂₁' : b₂ ≠ b₁ ^ 2 := by
    intro h
    have : altSixEmb e b₂ = altSixEmb e (b₁ ^ 2) := by rw [h]
    rw [map_pow, hb₁, hb₂, conj_pow] at this
    have := hcj _ _ this
    revert this; decide
  have hc₁₂ : b₁ ≠ b₁ * b₂ := by
    intro h
    apply hb₂1
    have := congrArg (fun w => b₁⁻¹ * w) h
    simpa using this.symm
  have hc₁₂' : b₁ ≠ (b₁ * b₂) ^ 2 := by
    intro h
    have : altSixEmb e b₁ = altSixEmb e ((b₁ * b₂) ^ 2) := by rw [← h]
    rw [map_pow, map_mul, hb₁, hb₂, hcm, conj_pow] at this
    have := hcj _ _ this
    revert this; decide
  have hr12 : (b₁ * b₂) ^ 3 = 1 := by
    rw [(show Commute b₁ b₂ from r3).mul_pow, r1, r2, one_mul]
  rcases hπ with h | h
  ·
    have hy1 : y = b₁ := hinj (by rw [hb₁, ← h])
    refine ⟨b₁, b₂, t, b₂, r1, r2, r3, r4, r5, r6, r7, ?_, ?_, ?_, ?_, r2⟩
    · rw [hy1]; exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [hy1]; exact not_mem_zpowers_of_pow_three r1 hb₂1 hc₂₁ hc₂₁'
    · rw [hy1]; exact r3.symm
  ·
    have hy1 : y = b₁ * b₂ := hinj (by rw [map_mul, hb₁, hb₂, hcm, ← h])
    refine ⟨b₁, b₂, t, b₁, r1, r2, r3, r4, r5, r6, r7, ?_, ?_, ?_, ?_, r1⟩
    · rw [hy1]; exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · rw [hy1]; exact not_mem_zpowers_of_pow_three hr12 hb₁1 hc₁₂ hc₁₂'
    · rw [hy1]; exact ((Commute.refl b₁).mul_right (show Commute b₁ b₂ from r3)).eq

end Abstract

end CFSG.CGT.PushingUpLit.CGT6
