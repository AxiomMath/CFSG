module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.ClaimA

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Branch

variable [Finite G] {t z : G}

theorem mem_pair_cases {x : G} (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : z * t = t * z)
    (hx : x ∈ pair z t) : x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  have hle : zpowers t ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute z t from hzt) k).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
  rcases eq_one_or_eq_of_mem_zpowers_two hz ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers_two ht hb with rfl | rfl <;> simp

theorem Level55.z_ne_t (d : Level55 G t z) : z ≠ t := fun h => d.t_not_mem (h ▸ d.z_mem_R0)

theorem Level55.R0_comm_t (d : Level55 G t z) {a : G} (ha : a ∈ d.R0) : a * t = t * a :=
  ((mem_centPair_iff.1 (d.R0_le ha)).2).symm

theorem Level55.exists_mul_of_mem_O2K (d : Level55 G t z) {r : G} (hr : r ∈ O2In (centPair z t)) :
    ∃ a ∈ d.R0, ∃ b ∈ zpowers t, r = a * b := by
  rw [d.O2K] at hr
  refine exists_mul_of_mem_sup_of_le_centralizer ?_ hr
  rw [zpowers_le, mem_centralizer_iff]
  intro a ha
  exact d.R0_comm_t ha


theorem Level55.mem_pair_of_central (d : Level55 G t z) {c : G} (hc : c ∈ O2In (centPair z t))
    (hcc : ∀ r ∈ O2In (centPair z t), c * r = r * c) : c ∈ pair z t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul_of_mem_O2K hc
  have hbR0 : ∀ a' ∈ d.R0, b * a' = a' * b := by
    intro a' ha'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_left (show Commute t a' from (d.R0_comm_t ha').symm) k).eq)
  have haz : a ∈ zpowers z := by
    have hcen : (⟨a, ha⟩ : ↥d.R0) ∈ center ↥d.R0 := by
      rw [mem_center_iff]
      intro a'
      apply Subtype.ext
      show (a' : G) * a = a * a'
      have h1 := hcc (a' : G) (d.R0_le_O2K a'.2)
      have h2 : a * (a' * b) = a' * (a * b) := by
        calc a * (a' * b) = a * (b * a') := by rw [hbR0 a' a'.2]
          _ = a * b * a' := by rw [mul_assoc]
          _ = a' * (a * b) := h1
      have h3 : a * a' * b = a' * a * b := by
        calc a * a' * b = a * (a' * b) := by rw [mul_assoc]
          _ = a' * (a * b) := h2
          _ = a' * a * b := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    have : a ∈ (center ↥d.R0).map d.R0.subtype := ⟨_, hcen, rfl⟩
    rw [d.R0_center] at this
    exact this
  exact mul_mem (mem_sup_left haz) (mem_sup_right hb)

theorem Level55.conj_t_eq_or (d : Level55 G t z) {g : G}
    (hgN : g ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G)) (hgz : g * z = z * g) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z := by
  have htR1 : t ∈ O2In (centPair z t) := d.pair_le_O2K (t_mem_pair z t)
  have hconj : ∀ r ∈ O2In (centPair z t), g * r * g⁻¹ ∈ O2In (centPair z t) := fun r hr =>
    (mem_normalizer_iff.1 hgN r).1 hr
  have hconj' : ∀ r ∈ O2In (centPair z t), g⁻¹ * r * g ∈ O2In (centPair z t) := by
    intro r hr
    refine (mem_normalizer_iff.1 hgN (g⁻¹ * r * g)).2 ?_
    have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    rw [e]
    exact hr
  have hR1K : O2In (centPair z t) ≤ centPair z t := O2In_le _
  have ht'R1 : g * t * g⁻¹ ∈ O2In (centPair z t) := hconj t htR1
  have ht'c : ∀ r ∈ O2In (centPair z t), g * t * g⁻¹ * r = r * (g * t * g⁻¹) := by
    intro r hr
    have hr' := hconj' r hr
    have htc : t * (g⁻¹ * r * g) = (g⁻¹ * r * g) * t :=
      mem_centralizer_iff.1 (hR1K hr') t (t_mem_pair z t)
    calc g * t * g⁻¹ * r = g * (t * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * t) * g⁻¹ := by rw [htc]
      _ = r * (g * t * g⁻¹) := by group
  have hmem := d.mem_pair_of_central ht'R1 ht'c
  rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hmem with h | h | h | h
  · exfalso
    have : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h2 := d.t_ord
    rw [this, orderOf_one] at h2
    exact absurd h2 (by decide)
  · exfalso
    apply d.z_ne_t
    calc z = g⁻¹ * z * g := by rw [mul_assoc, ← hgz, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  · left; exact h
  · right; rw [h, d.zt_comm]


theorem Level55.z_mul_self (d : Level55 G t z) : z * z = 1 := by
  rw [← pow_two, ← d.z_ord]; exact pow_orderOf_eq_one z

theorem inf_centPair_le_O2K (z t : G) : Psub z ⊓ centPair z t ≤ O2In (centPair z t) := by
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hPC : Psub z ≤ centZ z := O2In_le _
  have hn : ((Psub z ⊓ centPair z t).subgroupOf (centPair z t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    refine mem_inf.2 ⟨?_, (centPair z t).mul_mem ((centPair z t).mul_mem g.2 hn.2)
      ((centPair z t).inv_mem g.2)⟩
    have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨(n : G), hPC hn.1⟩
      (by rw [mem_subgroupOf]; exact hn.1) ⟨(g : G), hKC g.2⟩
    exact this
  have hp : IsPGroup 2 (Psub z ⊓ centPair z t : Subgroup G) :=
    (isPGroup_O2In _).to_le inf_le_left
  exact le_O2In inf_le_right hn hp

theorem Level55.exists_x_of_lt (d : Level55 G t z) (hlt : O2In (centPair z t) < Psub z) :
    ∃ x ∈ Psub z, x ∉ O2In (centPair z t) ∧ x * z = z * x ∧ x * t * x⁻¹ = t * z ∧
      x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G) ∧
      (∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t)) ∧
      x ^ 2 ∈ O2In (centPair z t) := by
  have hPC : Psub z ≤ centZ z := O2In_le _
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hR1P : O2In (centPair z t) ≤ Psub z := hlt.le
  have hPK := inf_centPair_le_O2K z t
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(Psub z) := (isPGroup_O2In (centZ z)).isNilpotent
  have hne : (O2In (centPair z t)).subgroupOf (Psub z) < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun h => hlt.not_ge ?_)
    exact Subgroup.subgroupOf_eq_top.1 h
  have hlt' := Group.normalizerCondition_of_isNilpotent _ hne
  obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt hlt'
  set x : G := (y : G) with hx
  have hxP : x ∈ Psub z := y.2
  have hxnot : x ∉ O2In (centPair z t) := fun h => hyH (mem_subgroupOf.2 h)
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (hPC hxP)
  have hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := (mem_normalizer_iff.1 hyN ⟨h, hR1P hh⟩).1 (mem_subgroupOf.2 hh)
      exact mem_subgroupOf.1 this
    · intro hh
      have hhP : h ∈ Psub z := by
        have h1 : x⁻¹ * (x * h * x⁻¹) * x ∈ Psub z :=
          mul_mem (mul_mem (inv_mem hxP) (hR1P hh)) hxP
        have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
        rwa [e] at h1
      have := (mem_normalizer_iff.1 hyN ⟨h, hhP⟩).2 (mem_subgroupOf.2 hh)
      exact mem_subgroupOf.1 this
  have hxt : x * t * x⁻¹ = t * z := by
    rcases d.conj_t_eq_or hxN hxz with h | h
    · exfalso
      apply hxnot
      apply hPK
      refine mem_inf.2 ⟨hxP, mem_centPair_iff.2 ⟨hxz.symm, ?_⟩⟩
      calc t * x = (x * t * x⁻¹) * x := by rw [h]
        _ = x * t := by group
    · exact h
  have hzz := d.z_mul_self
  have hxtx : x * t = t * z * x := by
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * z * x := by rw [hxt]
  have hxz' : x⁻¹ * z * x = z := by
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by rw [mul_assoc]
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  have hxz'' : x * z * x⁻¹ = z := by
    calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxz]
      _ = z := by group
  have hxinv_t : x⁻¹ * t * x = t * z := by
    have h1 : t = (x⁻¹ * t * x) * z := by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = x⁻¹ * (t * z) * x := by rw [hxt]
        _ = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
        _ = (x⁻¹ * t * x) * z := by rw [hxz']
    calc x⁻¹ * t * x = (x⁻¹ * t * x) * 1 := (mul_one _).symm
      _ = (x⁻¹ * t * x) * (z * z) := by rw [hzz]
      _ = ((x⁻¹ * t * x) * z) * z := by rw [← mul_assoc]
      _ = t * z := by rw [← h1]
  refine ⟨x, hxP, hxnot, hxz, hxt, hxN, ?_, ?_⟩
  · intro k hk
    obtain ⟨hkz, hkt⟩ := mem_centPair_iff.1 hk
    have hkC : k ∈ centZ z := hKC hk
    have hvP : x * k * x⁻¹ * k⁻¹ ∈ Psub z := by
      have h1 : k * x⁻¹ * k⁻¹ ∈ Psub z := by
        have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨x⁻¹, hPC (inv_mem hxP)⟩
          (by rw [mem_subgroupOf]; exact inv_mem hxP) ⟨k, hkC⟩
        exact this
      have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem hxP h1
    apply hPK
    refine mem_inf.2 ⟨hvP, mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 (hPC hvP)).symm,
      ?_⟩⟩
    have hkinv_t : k⁻¹ * t * k = t := by
      calc k⁻¹ * t * k = k⁻¹ * (t * k) := by rw [mul_assoc]
        _ = k⁻¹ * (k * t) := by rw [hkt]
        _ = t := by group
    have hk_tz : k * (t * z) * k⁻¹ = t * z := by
      calc k * (t * z) * k⁻¹ = (k * t) * z * k⁻¹ := by group
        _ = (t * k) * z * k⁻¹ := by rw [← hkt]
        _ = t * (k * z) * k⁻¹ := by group
        _ = t * (z * k) * k⁻¹ := by rw [← hkz]
        _ = t * z := by group
    have hvt : (x * k * x⁻¹ * k⁻¹) * t * (x * k * x⁻¹ * k⁻¹)⁻¹ = t := by
      calc (x * k * x⁻¹ * k⁻¹) * t * (x * k * x⁻¹ * k⁻¹)⁻¹
          = x * (k * (x⁻¹ * (k⁻¹ * t * k) * x) * k⁻¹) * x⁻¹ := by group
        _ = x * (k * (x⁻¹ * t * x) * k⁻¹) * x⁻¹ := by rw [hkinv_t]
        _ = x * (k * (t * z) * k⁻¹) * x⁻¹ := by rw [hxinv_t]
        _ = x * (t * z) * x⁻¹ := by rw [hk_tz]
        _ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
        _ = (t * z) * z := by rw [hxt, hxz'']
        _ = t := by rw [mul_assoc, hzz, mul_one]
    calc t * (x * k * x⁻¹ * k⁻¹) = (x * k * x⁻¹ * k⁻¹) * t := by
          have : (x * k * x⁻¹ * k⁻¹) * t = t * (x * k * x⁻¹ * k⁻¹) := by
            calc (x * k * x⁻¹ * k⁻¹) * t
                = ((x * k * x⁻¹ * k⁻¹) * t * (x * k * x⁻¹ * k⁻¹)⁻¹) * (x * k * x⁻¹ * k⁻¹) := by
                  group
              _ = t * (x * k * x⁻¹ * k⁻¹) := by rw [hvt]
          exact this.symm
      _ = (x * k * x⁻¹ * k⁻¹) * t := rfl
  · apply hPK
    refine mem_inf.2 ⟨pow_mem hxP 2, mem_centPair_iff.2 ⟨?_, ?_⟩⟩
    · calc z * x ^ 2 = z * x * x := by rw [pow_two, mul_assoc]
        _ = x * z * x := by rw [← hxz]
        _ = x * (z * x) := mul_assoc _ _ _
        _ = x * (x * z) := by rw [← hxz]
        _ = x ^ 2 * z := by rw [pow_two, mul_assoc]
    · have hx2t : x ^ 2 * t = t * x ^ 2 := by
        calc x ^ 2 * t = x * (x * t) := by rw [pow_two, mul_assoc]
          _ = x * (t * z * x) := by rw [hxtx]
          _ = (x * t) * z * x := by group
          _ = (t * z * x) * z * x := by rw [hxtx]
          _ = t * z * (x * z) * x := by group
          _ = t * z * (z * x) * x := by rw [hxz]
          _ = t * (z * z) * x * x := by group
          _ = t * x ^ 2 := by rw [hzz, pow_two]; group
      exact hx2t.symm

end Branch

end CFSG.EvenSporadicStandard.TwoB
