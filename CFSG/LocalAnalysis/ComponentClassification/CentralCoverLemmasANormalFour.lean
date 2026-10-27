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
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.ComponentClassification.CentralCover

open Subgroup
open scoped Pointwise commutatorElement

section Elementary

variable {C : Type*} [Group C]

private theorem mem_zpowers_of_orderOf_eq_four {x y : C} (hx : orderOf x = 4)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 ∨ y = x ^ 3 := by
  classical
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hx]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k <;> simp

private theorem mem_zpowers_of_orderOf_eq_two {x y : C} (hx : orderOf x = 2)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (by rw [hx]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hx] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k <;> simp

private theorem mul_mem_of_index_le_two [Finite C] {C₀ : Subgroup C} (hindex : C₀.index ≤ 2)
    {a b : C} (ha : a ∉ C₀) (hb : b ∉ C₀) : a * b ∈ C₀ := by
  have hne : C₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain h | h : C₀.index = 1 ∨ C₀.index = 2 := by omega
  · exact absurd ((index_eq_one.mp h) ▸ mem_top a) ha
  · exact (mul_mem_iff_of_index_two h).2 (iff_of_false ha hb)

private theorem normal_index_le_two_of_mul_mem {C₀ : Subgroup C}
    (h : ∀ a b, a ∉ C₀ → b ∉ C₀ → a * b ∈ C₀) : C₀.Normal ∧ C₀.index ≤ 2 := by
  by_cases htop : C₀ = ⊤
  · subst htop
    exact ⟨inferInstance, by simp⟩
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ C₀ := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun x _ => hcon x)
    have h2 : C₀.index = 2 := index_eq_two_iff.mpr ⟨a, fun b => by
      by_cases hb : b ∈ C₀
      · exact Or.inr ⟨hb, fun hba => ha (by simpa using C₀.mul_mem (C₀.inv_mem hb) hba)⟩
      · exact Or.inl ⟨by simpa using h b⁻¹⁻¹ a (by simpa using hb) ha, hb⟩⟩
    exact ⟨normal_of_index_eq_two h2, h2.le⟩

end Elementary

section NormalFour

variable {C : Type*} [Group C]

theorem index_two_normal_cyclic_four_central_involution_obstruction [Finite C]
    {C₀ : Subgroup C} (hC₀ : C₀.Normal) (hindex : C₀.index ≤ 2) {z : C}
    (hzcenter : z ∈ center C) (hzorder : orderOf z = 2) {B : Subgroup C} (hBC₀ : B ≤ C₀)
    (hBnormal : (B.subgroupOf C₀).Normal) (hBcyclic : IsCyclic B) (hBcard : Nat.card B = 4)
    (hzB : z ∈ B) :
    ∃ N : Subgroup C, N.Normal ∧
      (Nonempty (N ≃* Multiplicative (ZMod 4)) ∨
        Nonempty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) := by
  classical
  have hzc : ∀ g : C, g * z = z * g := mem_center_iff.mp hzcenter
  have hz2 : z ^ 2 = 1 := by rw [← hzorder]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by rintro rfl; simp at hzorder
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  obtain ⟨x₀, hx₀⟩ := hBcyclic.exists_ofOrder_eq_natCard
  set x : C := (x₀ : C) with hxdef
  have hxB : x ∈ B := x₀.2
  have hxorder : orderOf x = 4 := by rw [hxdef, Subgroup.orderOf_coe, hx₀, hBcard]
  have hBx : B = zpowers x := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxB)
    rw [Nat.card_zpowers, hxorder, hBcard]
  have hx4 : x ^ 4 = 1 := by rw [← hxorder]; exact pow_orderOf_eq_one x
  have hxsq1 : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hxorder]; norm_num)
  have hx2 : x ^ 2 = z := by
    rcases mem_zpowers_of_orderOf_eq_four hxorder (hBx ▸ hzB) with h | h | h | h
    · exact absurd h hz1
    · exact absurd (by rw [← h]; exact hz2) hxsq1
    · exact h.symm
    · exfalso
      apply hxsq1
      calc x ^ 2 = x ^ 4 * x ^ 2 := by rw [hx4, one_mul]
        _ = (x ^ 3) ^ 2 := by group
        _ = 1 := by rw [← h, hz2]
  have hBC₀norm : ∀ d ∈ C₀, ∀ b ∈ B, d * b * d⁻¹ ∈ B := by
    intro d hd b hb
    have h := hBnormal.conj_mem ⟨b, hBC₀ hb⟩ (mem_subgroupOf.mpr hb) ⟨d, hd⟩
    simpa [mem_subgroupOf] using h
  have hconj_gen : ∀ (g a : C) (K : Subgroup C), g * a * g⁻¹ ∈ K →
      ∀ n ∈ zpowers a, g * n * g⁻¹ ∈ K := by
    intro g a K hK n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact zpow_mem hK k
  have hfour : ∀ (a b : C), orderOf a = 4 → a ^ 2 = z → b ∈ zpowers a → b ^ 2 ≠ 1 →
      b = a ∨ b = a * z := by
    intro a b ha ha2 hb hb2
    rcases mem_zpowers_of_orderOf_eq_four ha hb with h | h | h | h
    · exact absurd (by rw [h, one_pow]) hb2
    · exact Or.inl h
    · exact absurd (by rw [h, ha2, hz2]) hb2
    · exact Or.inr (by rw [h, ← ha2]; group)
  by_cases hnorm : ∀ g : C, g * x * g⁻¹ ∈ B
  ·
    refine ⟨B, ⟨fun n hn g => hconj_gen g x B (hnorm g) n (hBx ▸ hn)⟩, Or.inl ⟨?_⟩⟩
    exact mulEquivOfCyclicCardEq (by rw [hBcard]; simp)
  push Not at hnorm
  obtain ⟨c, hc⟩ := hnorm
  have hcC₀ : c ∉ C₀ := fun h => hc (hBC₀norm c h x hxB)
  set y := c * x * c⁻¹ with hydef
  have hyC₀ : y ∈ C₀ := hC₀.conj_mem x (hBC₀ hxB) c
  have hyorder : orderOf y = 4 := by
    rw [hydef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxorder]
  have hy2 : y ^ 2 = z := by rw [hydef, conj_pow, hx2, hzc c, mul_inv_cancel_right]
  have hyB : y ∉ zpowers x := hBx ▸ hc
  have hxy : x ∉ zpowers y := by
    intro h
    apply hyB
    have hle : zpowers x ≤ zpowers y := zpowers_le.mpr h
    have heq : zpowers x = zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hxorder,
        hyorder])
    exact heq ▸ mem_zpowers y
  have hin_x : ∀ g ∈ C₀, g * x * g⁻¹ ∈ zpowers x := fun g hg => hBx ▸ hBC₀norm g hg x hxB
  have hout_x : ∀ g, g ∉ C₀ → g * x * g⁻¹ ∈ zpowers y := by
    intro g hg
    have hcinv : c⁻¹ ∉ C₀ := fun h => hcC₀ (by simpa using C₀.inv_mem h)
    have hd : c⁻¹ * g ∈ C₀ := mul_mem_of_index_le_two hindex hcinv hg
    have h := hin_x _ hd
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    rw [mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [hydef, conj_zpow, hk]
    group
  have hin_y : ∀ g ∈ C₀, g * y * g⁻¹ ∈ zpowers y := by
    intro g hg
    have hgc : g * c ∉ C₀ := fun h => hcC₀ (by simpa using C₀.mul_mem (C₀.inv_mem hg) h)
    have h := hout_x _ hgc
    rwa [show g * c * x * (g * c)⁻¹ = g * y * g⁻¹ by rw [hydef]; group] at h
  have hout_y : ∀ g, g ∉ C₀ → g * y * g⁻¹ ∈ zpowers x := by
    intro g hg
    have h := hin_x _ (mul_mem_of_index_le_two hindex hg hcC₀)
    rwa [show g * c * x * (g * c)⁻¹ = g * y * g⁻¹ by rw [hydef]; group] at h
  have hcommx : x * y * x⁻¹ * y⁻¹ ∈ zpowers x := by
    have h := hin_x _ hyC₀
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x * y⁻¹)⁻¹ by group]
    exact mul_mem (mem_zpowers x) (inv_mem h)
  have hcommy : x * y * x⁻¹ * y⁻¹ ∈ zpowers y :=
    mul_mem (hin_y _ (hBC₀ hxB)) (inv_mem (mem_zpowers y))
  have hcomm : x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
    rcases mem_zpowers_of_orderOf_eq_four hxorder hcommx with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hcommy) hxy
    · exact Or.inr (h.trans hx2)
    · refine absurd ?_ hxy
      have : (x ^ 3)⁻¹ ∈ zpowers y := inv_mem (h ▸ hcommy)
      rwa [show (x ^ 3)⁻¹ = x by
        calc (x ^ 3)⁻¹ = (x ^ 3)⁻¹ * x ^ 4 := by rw [hx4, mul_one]
          _ = x := by group] at this
  rcases hcomm with hab | hnab
  ·
    have hxyc : Commute x y := by
      rw [show x * y * x⁻¹ * y⁻¹ = ⁅x, y⁆ from rfl, commutatorElement_eq_one_iff_mul_comm] at hab
      exact hab
    set N := closure ({x, y} : Set C) with hNdef
    have hxN : x ∈ N := subset_closure (by simp)
    have hyN : y ∈ N := subset_closure (by simp)
    have hNnormal : N.Normal := ⟨fun n hn g => by
      induction hn using Subgroup.closure_induction with
      | mem a ha =>
        rcases ha with rfl | ha
        · by_cases hg : g ∈ C₀
          · exact zpowers_le.mpr hxN (hin_x g hg)
          · exact zpowers_le.mpr hyN (hout_x g hg)
        · rw [Set.mem_singleton_iff] at ha
          subst ha
          by_cases hg : g ∈ C₀
          · exact zpowers_le.mpr hyN (hin_y g hg)
          · exact zpowers_le.mpr hxN (hout_y g hg)
      | one => simp
      | mul a b _ _ iha ihb =>
        rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
        exact mul_mem iha ihb
      | inv a _ iha =>
        rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
        exact inv_mem iha⟩
    set w := x⁻¹ * y with hwdef
    have hwx : Commute w x := (Commute.inv_left (Commute.refl x)).mul_left hxyc.symm
    have hw2 : w ^ 2 = 1 := by
      rw [hwdef, (Commute.inv_left hxyc).mul_pow, inv_pow, hx2, hy2, inv_mul_cancel]
    have hw1 : w ≠ 1 := by
      intro h
      apply hyB
      rw [hwdef, inv_mul_eq_one] at h
      exact h ▸ mem_zpowers x
    have hworder : orderOf w = 2 := orderOf_eq_prime hw2 hw1
    have hyxw : y = x * w := by rw [hwdef]; group
    have hwB : w ∉ zpowers x := fun h => hyB (hyxw ▸ mul_mem (mem_zpowers x) h)
    have hwN : w ∈ N := mul_mem (inv_mem hxN) hyN
    let e₁ : Multiplicative (ZMod 2) ≃* zpowers w :=
      mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, hworder]; simp)
    let e₂ : Multiplicative (ZMod 4) ≃* zpowers x :=
      mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, hxorder]; simp)
    let f₁ : Multiplicative (ZMod 2) →* C := (zpowers w).subtype.comp e₁.toMonoidHom
    let f₂ : Multiplicative (ZMod 4) →* C := (zpowers x).subtype.comp e₂.toMonoidHom
    have hf₁ : ∀ a, f₁ a ∈ zpowers w := fun a => (e₁ a).2
    have hf₂ : ∀ b, f₂ b ∈ zpowers x := fun b => (e₂ b).2
    have hcomm12 : ∀ a b, Commute (f₁ a) (f₂ b) := by
      intro a b
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hf₁ a)
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hf₂ b)
      rw [← hi, ← hj]
      exact hwx.zpow_zpow i j
    let Φ := MonoidHom.noncommCoprod f₁ f₂ hcomm12
    have hΦ : ∀ p, Φ p = f₁ p.1 * f₂ p.2 := fun p => MonoidHom.noncommCoprod_apply _ _ _ p
    have hinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      rw [hΦ] at hab
      have ha : f₁ a = 1 := by
        have hmem : f₁ a ∈ zpowers x := by
          rw [eq_inv_of_mul_eq_one_left hab]
          exact inv_mem (hf₂ b)
        rcases mem_zpowers_of_orderOf_eq_two hworder (hf₁ a) with h | h
        · exact h
        · exact absurd (h ▸ hmem) hwB
      have hb : f₂ b = 1 := by rwa [ha, one_mul] at hab
      have ha' : a = 1 := e₁.injective (Subtype.ext (by simpa [f₁] using ha))
      have hb' : b = 1 := e₂.injective (Subtype.ext (by simpa [f₂] using hb))
      simp [ha', hb']
    have hrange : Φ.range = N := by
      apply le_antisymm
      · rintro _ ⟨p, rfl⟩
        rw [hΦ]
        exact mul_mem (zpowers_le.mpr hwN (hf₁ p.1)) (zpowers_le.mpr hxN (hf₂ p.2))
      · have hxr : x ∈ Φ.range := ⟨(1, e₂.symm ⟨x, mem_zpowers x⟩), by simp [hΦ, f₂]⟩
        have hwr : w ∈ Φ.range := ⟨(e₁.symm ⟨w, mem_zpowers w⟩, 1), by simp [hΦ, f₁]⟩
        rw [hNdef, closure_le]
        intro a ha
        rcases ha with rfl | ha
        · exact hxr
        · rw [Set.mem_singleton_iff] at ha
          rw [ha, hyxw]
          exact mul_mem hxr hwr
    exact ⟨N, hNnormal, Or.inr
      ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩⟩
  ·
    have hyx : y * x = z * (x * y) := by
      have hxy' : x * y = z * (y * x) := by
        calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
          _ = z * (y * x) := by rw [hnab]
      rw [hxy', ← mul_assoc, hzz, one_mul]
    have hq2 : (x * y) ^ 2 = z := by
      calc (x * y) ^ 2 = x * (y * x) * y := by simp only [sq, mul_assoc]
        _ = x * (z * (x * y)) * y := by rw [hyx]
        _ = z * (x ^ 2 * y ^ 2) := by rw [← mul_assoc x z, hzc x]; simp only [sq, mul_assoc]
        _ = z := by rw [hx2, hy2, ← mul_assoc, hzz, one_mul]
    have hqorder : orderOf (x * y) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x * y)
        (by rw [pow_one, hq2]; exact hz1) (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num,
          pow_mul, hq2, hz2])
      rw [h]
      norm_num
    have hzq : z ∈ zpowers (x * y) := hq2 ▸ pow_mem (mem_zpowers _) 2
    have hsqx : ∀ g : C, (g * x * g⁻¹) ^ 2 ≠ 1 := by
      intro g
      rw [conj_pow, hx2, hzc g, mul_inv_cancel_right]
      exact hz1
    have hsqy : ∀ g : C, (g * y * g⁻¹) ^ 2 ≠ 1 := by
      intro g
      rw [conj_pow, hy2, hzc g, mul_inv_cancel_right]
      exact hz1
    have hform : ∀ a b : C, orderOf a = 4 → a ^ 2 = z → b ∈ zpowers a → b ^ 2 ≠ 1 →
        ∃ m : C, (m = 1 ∨ m = z) ∧ b = a * m := by
      intro a b ha ha2 hb hb2
      rcases hfour a b ha ha2 hb hb2 with h | h
      · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
      · exact ⟨z, Or.inr rfl, h⟩
    have hcentral : ∀ m : C, (m = 1 ∨ m = z) →
        (∀ g : C, g * m = m * g) ∧ m ∈ zpowers (x * y) := by
      intro m hm
      rcases hm with hm | hm
      · subst hm
        exact ⟨fun g => by simp, one_mem _⟩
      · rw [hm]
        exact ⟨hzc, hzq⟩
    have hkey : ∀ m₁ m₂ : C, (m₁ = 1 ∨ m₁ = z) → (m₂ = 1 ∨ m₂ = z) →
        x * m₁ * (y * m₂) ∈ zpowers (x * y) ∧ y * m₁ * (x * m₂) ∈ zpowers (x * y) := by
      intro m₁ m₂ hm₁ hm₂
      obtain ⟨hc₁, hq₁⟩ := hcentral m₁ hm₁
      obtain ⟨-, hq₂⟩ := hcentral m₂ hm₂
      constructor
      · rw [show x * m₁ * (y * m₂) = x * y * (m₁ * m₂) by
          rw [mul_assoc x m₁, ← mul_assoc m₁ y, ← hc₁ y]; group]
        exact mul_mem (mem_zpowers _) (mul_mem hq₁ hq₂)
      · rw [show y * m₁ * (x * m₂) = y * x * (m₁ * m₂) by
          rw [mul_assoc y m₁, ← mul_assoc m₁ x, ← hc₁ x]; group, hyx]
        exact mul_mem (mul_mem hzq (mem_zpowers _)) (mul_mem hq₁ hq₂)
    refine ⟨zpowers (x * y), ⟨fun n hn g => hconj_gen g (x * y) _ ?_ n hn⟩,
      Or.inl ⟨mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, hqorder]; simp)⟩⟩
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    by_cases hg : g ∈ C₀
    · obtain ⟨m₁, hm₁, ha⟩ := hform x _ hxorder hx2 (hin_x g hg) (hsqx g)
      obtain ⟨m₂, hm₂, hb⟩ := hform y _ hyorder hy2 (hin_y g hg) (hsqy g)
      rw [ha, hb]
      exact (hkey m₁ m₂ hm₁ hm₂).1
    · obtain ⟨m₁, hm₁, ha⟩ := hform y _ hyorder hy2 (hout_x g hg) (hsqx g)
      obtain ⟨m₂, hm₂, hb⟩ := hform x _ hxorder hx2 (hout_y g hg) (hsqy g)
      rw [ha, hb]
      exact (hkey m₁ m₂ hm₁ hm₂).2

end NormalFour

section CyclicKernel

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq (g a : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) a
  rwa [MulAut.conj_apply] at h

private theorem orderOf_inv_conj_eq (g a : G) : orderOf (g⁻¹ * a * g) = orderOf a := by
  have h := orderOf_conj_eq g⁻¹ a
  rwa [inv_inv] at h

private theorem inv_conj_zpow (g a : G) (k : ℤ) : (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
  have h := conj_zpow (i := k) (a := g⁻¹) (b := a)
  rwa [inv_inv] at h

private theorem inv_conj_pow (g a : G) (k : ℕ) : (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
  have h := conj_pow (i := k) (a := g⁻¹) (b := a)
  rwa [inv_inv] at h

private theorem mem_zpowers_of_orderOf_eq [Finite G] {S : Subgroup G} (hS : IsCyclic S)
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) (hab : orderOf a = orderOf b) : a ∈ zpowers b := by
  have h : zpowers (⟨a, ha⟩ : S) = zpowers ⟨b, hb⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hab])
  have hmem : (⟨a, ha⟩ : S) ∈ zpowers ⟨b, hb⟩ := h ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem eq_of_orderOf_eq_two [Finite G] {S : Subgroup G} (hS : IsCyclic S) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  rcases mem_zpowers_of_orderOf_eq_two hb2
    (mem_zpowers_of_orderOf_eq hS ha hb (ha2.trans hb2.symm)) with h | h
  · rw [h, orderOf_one] at ha2
    omega
  · exact h

theorem cyclic_centralizer_kernel_small_normal_four_obstruction [Finite G] {S : Subgroup G}
    (hScyclic : IsCyclic S) (hS2 : IsPGroup 2 S) (hScard : 4 ≤ Nat.card S) {t : G}
    (htS : t ∈ S) (htorder : orderOf t = 2) {H : Subgroup G}
    (hH : H = Subgroup.centralizer {t}) (hSH : (S.subgroupOf H).Normal)
    (hsquare : ∀ h ∈ H, ∀ s ∈ S, h ^ 2 * s = s * h ^ 2) {J : Type*} [Group J]
    (θ : H →* J) (hθ : Function.Surjective θ) (hker : θ.ker = S.subgroupOf H)
    (hJ : ∀ v : J, orderOf v = 2 → ∀ N : Subgroup (Subgroup.centralizer {v}), N.Normal →
      ¬ (Nonempty (N ≃* Multiplicative (ZMod 4)) ∨
        Nonempty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))))
    (g : G) (hg : MulAut.conj g⁻¹ • S ≤ H) : MulAut.conj g⁻¹ • S = S ∧ g ∈ H := by
  classical
  subst hH
  have : Finite J := Finite.of_surjective θ hθ
  have hmem : ∀ x, x ∈ MulAut.conj g⁻¹ • S ↔ g * x * g⁻¹ ∈ S := by
    intro x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
      MulAut.conj_apply]
  have := hScyclic
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := S)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hSC : S ≤ Subgroup.centralizer {t} := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hSab s hs t htS)
  have hSnorm : ∀ h ∈ Subgroup.centralizer {t}, ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
    intro h hh s hs
    have h' := hSH.conj_mem ⟨s, hSC hs⟩ (mem_subgroupOf.mpr hs) ⟨h, hh⟩
    simpa [mem_subgroupOf] using h'
  have hinvol : ∀ a ∈ S, orderOf a = 2 → a = t := fun a ha ha2 =>
    eq_of_orderOf_eq_two hScyclic ha htS ha2 htorder
  have hsq1 : ∀ s ∈ S, s ^ 2 = 1 → s = 1 ∨ s = t := by
    intro s hs hs2
    by_cases h1 : s = 1
    · exact Or.inl h1
    · exact Or.inr (hinvol s hs (orderOf_eq_prime hs2 h1))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have h4 : 4 ∣ Nat.card S := by
    rw [hn]
    have h2n : 2 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n <;> simp_all
    exact (pow_dvd_pow 2 h2n : 2 ^ 2 ∣ 2 ^ n)
  set s₀ : G := ((γ ^ (orderOf γ / 4) : S) : G) with hs₀def
  have hs₀S : s₀ ∈ S := (γ ^ (orderOf γ / 4)).2
  have hs₀order : orderOf s₀ = 4 := by
    rw [hs₀def, Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (by rw [hγ]; exact Nat.card_pos.ne') (by rw [hγ]; exact h4)
  have hs₀sq : s₀ ^ 2 = t := by
    apply hinvol _ (pow_mem hs₀S 2)
    have h := orderOf_pow_orderOf_div (x := s₀) (n := 2) (by rw [hs₀order]; norm_num)
      (by rw [hs₀order]; norm_num)
    rwa [hs₀order] at h
  have hmain : MulAut.conj g⁻¹ • S = S := by
    by_contra hne
    set u := g⁻¹ * t * g with hudef
    have hgu : g * u * g⁻¹ = t := by rw [hudef]; group
    have huS' : u ∈ MulAut.conj g⁻¹ • S := by rw [hmem, hgu]; exact htS
    have huorder : orderOf u = 2 := by rw [hudef, orderOf_inv_conj_eq, htorder]
    have hu2 : u ^ 2 = 1 := by rw [← huorder]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at huorder
      omega
    have hut : u ≠ t := by
      intro hut
      apply hne
      have hgc : g ∈ Subgroup.centralizer {t} := by
        rw [mem_centralizer_singleton_iff]
        have h : g * u = t * g := by rw [hudef]; group
        rwa [hut] at h
      have hginv : g⁻¹ ∈ Subgroup.centralizer {t} := inv_mem hgc
      ext x
      rw [hmem]
      constructor
      · intro hx
        have h := hSnorm _ hginv _ hx
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h
      · intro hx
        exact hSnorm _ hgc _ hx
    have hinter : ∀ x ∈ S, x ∈ MulAut.conj g⁻¹ • S → x = 1 := by
      intro x hxS hxS'
      by_contra hx1
      have hxord : orderOf x ∣ 2 ^ n := by rw [← hn]; exact Subgroup.orderOf_dvd_natCard S hxS
      obtain ⟨k, -, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxord
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hxk
        exact hx1 hxk
      have h2 : 2 ∣ orderOf x := by rw [hxk]; exact dvd_pow_self 2 hk0
      have hyorder : orderOf (x ^ (orderOf x / 2)) = 2 :=
        orderOf_pow_orderOf_div (orderOf_pos x).ne' h2
      have hyt : x ^ (orderOf x / 2) = t := hinvol _ (pow_mem hxS _) hyorder
      have hgy : g * x ^ (orderOf x / 2) * g⁻¹ = t :=
        hinvol _ ((hmem _).mp (pow_mem hxS' _)) (by rw [orderOf_conj_eq, hyorder])
      rw [hyt] at hgy
      apply hut
      rw [hudef]
      calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [hgy]
        _ = t := by group
    set w := g⁻¹ * s₀ * g with hwdef
    have hgw : g * w * g⁻¹ = s₀ := by rw [hwdef]; group
    have hwS' : w ∈ MulAut.conj g⁻¹ • S := by rw [hmem, hgw]; exact hs₀S
    have hwH : w ∈ Subgroup.centralizer {t} := hg hwS'
    have hw2 : w ^ 2 = u := by rw [hwdef, inv_conj_pow, hs₀sq]
    have huS : ∀ s ∈ S, u * s = s * u := by
      intro s hs
      have h := hsquare w hwH s hs
      rwa [hw2] at h
    have huH : u ∈ Subgroup.centralizer {t} := hg huS'
    set uH : Subgroup.centralizer {t} := ⟨u, huH⟩ with huHdef
    set wH : Subgroup.centralizer {t} := ⟨w, hwH⟩ with hwHdef
    have hθinj : ∀ x : Subgroup.centralizer {t}, (x : G) ∈ MulAut.conj g⁻¹ • S → θ x = 1 →
        (x : G) = 1 := by
      intro x hxS' hx1
      have hxker : x ∈ θ.ker := hx1
      rw [hker, mem_subgroupOf] at hxker
      exact hinter _ hxker hxS'
    set v := θ uH with hvdef
    have huH2 : uH ^ 2 = 1 := Subtype.ext (by simp [huHdef, hu2])
    have hvorder : orderOf v = 2 := by
      apply orderOf_eq_prime
      · rw [hvdef, ← map_pow, huH2, map_one]
      · intro hv1
        exact hu1 (hθinj uH huS' hv1)
    have hv1 : v ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hvorder
      omega
    have hwv : θ wH ^ 2 = v := by
      rw [hvdef, ← map_pow]
      congr 1
      exact Subtype.ext (by simp [hwHdef, huHdef, hw2])
    have hθw : orderOf (θ wH) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := θ wH)
        (by rw [pow_one, hwv]; exact hv1)
        (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hwv, ← hvorder,
          pow_orderOf_eq_one])
      rw [h]
      norm_num
    have hA : ∀ h : Subgroup.centralizer {t}, θ h * v = v * θ h →
        (h : G) * u * (h : G)⁻¹ = u ∨ (h : G) * u * (h : G)⁻¹ = u * t := by
      intro h hcomm
      have hk : uH⁻¹ * (h * uH * h⁻¹) ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hvdef, hcomm]
        group
      rw [hker, mem_subgroupOf] at hk
      have hsS : u⁻¹ * ((h : G) * u * (h : G)⁻¹) ∈ S := by simpa [huHdef] using hk
      set s := u⁻¹ * ((h : G) * u * (h : G)⁻¹) with hsdef
      have hus : (h : G) * u * (h : G)⁻¹ = u * s := by rw [hsdef]; group
      have hs2 : s ^ 2 = 1 := by
        have h1 : ((h : G) * u * (h : G)⁻¹) ^ 2 = 1 := by rw [conj_pow, hu2]; group
        rwa [hus, (show Commute u s from huS s hsS).mul_pow 2, hu2, one_mul] at h1
      rcases hsq1 s hsS hs2 with h1 | h1
      · left
        rw [hus, h1, mul_one]
      · right
        rw [hus, h1]
    set K := Subgroup.centralizer ({v} : Set J) with hKdef
    set D : Subgroup (Subgroup.centralizer {t}) :=
      (Subgroup.centralizer {u}).subgroupOf (Subgroup.centralizer {t}) with hDdef
    set C₀ : Subgroup K := (D.map θ).subgroupOf K with hC₀def
    have hnot : ∀ (x : K) (x' : Subgroup.centralizer {t}), θ x' = (x : J) → x ∉ C₀ →
        (x' : G) * u * (x' : G)⁻¹ = u * t := by
      intro x x' hx' hx
      have hcx : θ x' * v = v * θ x' := by
        rw [hx']
        exact mem_centralizer_singleton_iff.mp x.2
      rcases hA x' hcx with h | h
      · exfalso
        apply hx
        rw [hC₀def, mem_subgroupOf]
        refine ⟨x', ?_, hx'⟩
        show x' ∈ D
        rw [hDdef, mem_subgroupOf, mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp h
      · exact h
    have hC₀mul : ∀ a b : K, a ∉ C₀ → b ∉ C₀ → a * b ∈ C₀ := by
      intro a b ha hb
      obtain ⟨ha', hha⟩ := hθ (a : J)
      obtain ⟨hb', hhb⟩ := hθ (b : J)
      have ha2 := hnot a ha' hha ha
      have hb2 := hnot b hb' hhb hb
      rw [hC₀def, mem_subgroupOf]
      refine ⟨ha' * hb', ?_, by rw [map_mul, hha, hhb]; rfl⟩
      show ha' * hb' ∈ D
      rw [hDdef, mem_subgroupOf, mem_centralizer_singleton_iff]
      have hat : (ha' : G) * t * (ha' : G)⁻¹ = t := by
        rw [mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_singleton_iff.mp ha'.2
      have key : ((ha' * hb' : Subgroup.centralizer {t}) : G) * u *
          ((ha' * hb' : Subgroup.centralizer {t}) : G)⁻¹ = u := by
        rw [coe_mul, mul_inv_rev]
        calc (ha' : G) * hb' * u * ((hb' : G)⁻¹ * (ha' : G)⁻¹)
            = (ha' : G) * ((hb' : G) * u * (hb' : G)⁻¹) * (ha' : G)⁻¹ := by group
          _ = (ha' : G) * (u * t) * (ha' : G)⁻¹ := by rw [hb2]
          _ = ((ha' : G) * u * (ha' : G)⁻¹) * ((ha' : G) * t * (ha' : G)⁻¹) := by group
          _ = u * t * t := by rw [ha2, hat]
          _ = u := by rw [mul_assoc, ← sq, ← htorder, pow_orderOf_eq_one, mul_one]
      exact mul_inv_eq_iff_eq_mul.mp key
    obtain ⟨hC₀normal, hC₀index⟩ := normal_index_le_two_of_mul_mem hC₀mul
    set vK : K := ⟨v, mem_centralizer_singleton_iff.mpr rfl⟩ with hvKdef
    set wK : K := ⟨θ wH, mem_centralizer_singleton_iff.mpr (by
      rw [← hwv]; exact (Commute.self_pow (θ wH) 2).eq)⟩ with hwKdef
    have hvKcenter : vK ∈ center K :=
      mem_center_iff.mpr fun k => Subtype.ext (mem_centralizer_singleton_iff.mp k.2)
    have hvKorder : orderOf vK = 2 := by rw [hvKdef, Subgroup.orderOf_mk, hvorder]
    have hwD : wH ∈ D := by
      rw [hDdef, mem_subgroupOf, mem_centralizer_singleton_iff]
      rw [← hw2]
      exact (Commute.self_pow w 2).eq
    have hBC₀ : zpowers wK ≤ C₀ := by
      rw [zpowers_le, hC₀def, mem_subgroupOf]
      exact ⟨wH, hwD, rfl⟩
    have hBcard : Nat.card (zpowers wK) = 4 := by
      rw [Nat.card_zpowers, hwKdef, Subgroup.orderOf_mk, hθw]
    have hvKB : vK ∈ zpowers wK := by
      have h : wK ^ 2 = vK := Subtype.ext (by simp [hwKdef, hvKdef, hwv])
      exact h ▸ pow_mem (mem_zpowers wK) 2
    have hconjw : ∀ d ∈ D, ∃ k : ℤ, d * wH * d⁻¹ = wH ^ k := by
      intro d hd
      rw [hDdef, mem_subgroupOf, mem_centralizer_singleton_iff] at hd
      have hgd : g * (d : G) * g⁻¹ ∈ Subgroup.centralizer {t} := by
        rw [mem_centralizer_singleton_iff]
        calc g * (d : G) * g⁻¹ * t = g * (d : G) * g⁻¹ * (g * u * g⁻¹) := by rw [hgu]
          _ = g * ((d : G) * u) * g⁻¹ := by group
          _ = g * (u * (d : G)) * g⁻¹ := by rw [hd]
          _ = (g * u * g⁻¹) * (g * (d : G) * g⁻¹) := by group
          _ = t * (g * (d : G) * g⁻¹) := by rw [hgu]
      have hmemS : g * ((d : G) * w * (d : G)⁻¹) * g⁻¹ ∈ S := by
        rw [show g * ((d : G) * w * (d : G)⁻¹) * g⁻¹ =
          (g * (d : G) * g⁻¹) * s₀ * (g * (d : G) * g⁻¹)⁻¹ by rw [hwdef]; group]
        exact hSnorm _ hgd _ hs₀S
      have hord : orderOf (g * ((d : G) * w * (d : G)⁻¹) * g⁻¹) = orderOf s₀ := by
        rw [orderOf_conj_eq, orderOf_conj_eq, hwdef, orderOf_inv_conj_eq]
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_zpowers_of_orderOf_eq hScyclic hmemS hs₀S hord)
      refine ⟨k, Subtype.ext ?_⟩
      simp only [coe_mul, coe_inv, SubgroupClass.coe_zpow, hwHdef]
      have hwk : w ^ k = g⁻¹ * s₀ ^ k * g := by rw [hwdef, inv_conj_zpow]
      rw [hwk, hk]
      group
    have hBnormal : ((zpowers wK).subgroupOf C₀).Normal := by
      constructor
      intro n hn c
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
      have hc : ((c : K) : J) ∈ D.map θ := c.2
      obtain ⟨d, hd, hdc⟩ := hc
      obtain ⟨m, hm⟩ := hconjw d hd
      refine mem_zpowers_iff.mpr ⟨m * k, Subtype.ext ?_⟩
      have hnJ : ((n : K) : J) = θ wH ^ k := by rw [← hk]; simp [hwKdef]
      simp only [coe_mul, coe_inv, SubgroupClass.coe_zpow, hwKdef]
      rw [hnJ, ← hdc, ← conj_zpow, ← map_inv, ← map_mul, ← map_mul, hm, map_zpow, ← zpow_mul]
    obtain ⟨N, hN, hiso⟩ := index_two_normal_cyclic_four_central_involution_obstruction
      hC₀normal hC₀index hvKcenter hvKorder hBC₀ hBnormal inferInstance hBcard hvKB
    exact hJ v hvorder N hN hiso
  refine ⟨hmain, ?_⟩
  have h1 : g⁻¹ * t * g ∈ MulAut.conj g⁻¹ • S := (hmem _).mpr (by
    rw [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    exact htS)
  rw [hmain] at h1
  have hu : g⁻¹ * t * g = t := hinvol _ h1 (by rw [orderOf_inv_conj_eq, htorder])
  rw [mem_centralizer_singleton_iff]
  calc g * t = g * (g⁻¹ * t * g) := by rw [hu]
    _ = t * g := by group

end CyclicKernel

end CFSG.ComponentClassification.CentralCover
