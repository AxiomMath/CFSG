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

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup

namespace Irr

theorem card_modEq_one_of_aut_five {X : Type} [Group X] [Finite X] (α : MulAut X)
    (h5 : α ^ 5 = 1) (hfix : ∀ x : X, α x = x → x = 1) : Nat.card X ≡ 1 [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Γ : Subgroup (MulAut X) := Subgroup.zpowers α with hΓ
  have hord : orderOf α ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hΓp : IsPGroup 5 Γ := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hord with h | h
    · refine IsPGroup.of_card (n := 0) ?_
      rw [hΓ, Nat.card_zpowers, h]; simp
    · refine IsPGroup.of_card (n := 1) ?_
      rw [hΓ, Nat.card_zpowers, h]; simp
  have hmod := hΓp.card_modEq_card_fixedPoints (α := X)
  have hfixcard : Nat.card (MulAction.fixedPoints Γ X) = 1 := by
    have : MulAction.fixedPoints Γ X = {1} := by
      ext x
      constructor
      · intro hx
        have := hx ⟨α, Subgroup.mem_zpowers α⟩
        exact hfix x this
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        intro g
        exact map_one g.1
    rw [this]
    simp
  rw [hfixcard] at hmod
  exact hmod

theorem nat_dvd16_mod5 : ∀ n : ℕ, n ∣ 16 → n % 5 = 1 → n = 1 ∨ n = 16 := by
  intro n hn hmod
  have hle : n ≤ 16 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n <;> omega

theorem irr_of_aut_five {Hb : Type} [Group Hb] [Finite Hb] {R Z : Subgroup Hb} (y : Hb)
    (hZc : ∀ w ∈ Z, ∀ r ∈ R, w * r = r * w)
    (hcard : Nat.card R = 16 * Nat.card Z)
    (hyZ : ∀ w ∈ Z, y * w * y⁻¹ ∈ Z)
    (hfpf : ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ Z → r ∈ Z)
    (hper : ∀ r ∈ R, y ^ 5 * r * (y ^ 5)⁻¹ * r⁻¹ ∈ Z)
    (U : Subgroup Hb) (hZU : Z ≤ U) (hUR : U ≤ R) (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    U = Z ∨ U = R := by
  classical
  have hZn : (Z.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hZc _ hn g (hUR g.2)
    have : ((g * n * g⁻¹ : ↥U) : Hb) = (n : Hb) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : Hb) * n * (g : Hb)⁻¹ = ((n : Hb) * g) * (g : Hb)⁻¹ := by rw [h1]
        _ = n := by group
    rw [this]; exact hn
  let ψ : ↥U →* ↥U := ((MulAut.conj y).toMonoidHom.comp U.subtype).codRestrict U
    (fun u => by simpa [MulAut.conj_apply] using hyU u u.2)
  have hψinj : Function.Injective ψ := by
    intro a b h
    have h1 : y * (a : Hb) * y⁻¹ = y * (b : Hb) * y⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hψbij : Function.Bijective ψ := ⟨hψinj, Finite.injective_iff_surjective.mp hψinj⟩
  let ψ' : ↥U ≃* ↥U := MulEquiv.ofBijective ψ hψbij
  have hψ'app : ∀ u : ↥U, ((ψ' u : ↥U) : Hb) = y * (u : Hb) * y⁻¹ := fun u => rfl
  have hmap : (Z.subgroupOf U).map ψ'.toMonoidHom = Z.subgroupOf U := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_subgroupOf.mp (show w ∈ Z.subgroupOf U from hw)
      exact Subgroup.mem_subgroupOf.mpr (by
        show y * (w : Hb) * y⁻¹ ∈ Z
        exact hyZ _ hw')
    · rw [Subgroup.card_map_of_injective (f := ψ'.toMonoidHom) ψ'.injective]
  let α : MulAut (↥U ⧸ Z.subgroupOf U) :=
    QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) ψ' hmap
  have hαapp : ∀ u : ↥U, α (QuotientGroup.mk u) = QuotientGroup.mk (ψ' u) := fun u => rfl
  have hψpow : ∀ (k : ℕ) (u : ↥U), (((ψ' ^ k) u : ↥U) : Hb) = y ^ k * (u : Hb) * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, ih, hψ'app]
      simp only [pow_succ]
      group
  have hpow : ∀ (k : ℕ) (u : ↥U),
      (α ^ k) (QuotientGroup.mk u) = QuotientGroup.mk ((ψ' ^ k) u) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hαapp]
      exact ih (ψ' u)
  have hα5 : α ^ 5 = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [hpow]
      show QuotientGroup.mk ((ψ' ^ 5) u) = QuotientGroup.mk u
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := hper ((u : Hb)⁻¹) (U.inv_mem u.2 |> hUR)
      have h2 : ((((ψ' ^ 5) u)⁻¹ * u : ↥U) : Hb) =
          y ^ 5 * (u : Hb)⁻¹ * (y ^ 5)⁻¹ * ((u : Hb)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψpow]
        group
      rw [h2]; exact h1
  have hfix : ∀ x : ↥U ⧸ Z.subgroupOf U, α x = x → x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      intro h
      rw [hαapp] at h
      have h' := QuotientGroup.eq.mp h
      rw [Subgroup.mem_subgroupOf] at h'
      have h2 : ((((ψ' u)⁻¹ * u : ↥U)) : Hb) = y * (u : Hb)⁻¹ * y⁻¹ * ((u : Hb)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ'app]
        group
      rw [h2] at h'
      have hu : (u : Hb)⁻¹ ∈ Z := hfpf _ (hUR (U.inv_mem u.2)) h'
      have hu' : (u : Hb) ∈ Z := by simpa using Z.inv_mem hu
      exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr hu')
  have hmod := card_modEq_one_of_aut_five α hα5 hfix
  have hUcard : Nat.card U = Nat.card (↥U ⧸ Z.subgroupOf U) * Nat.card Z := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
    exact h1
  have hdvd : Nat.card U ∣ Nat.card R := Subgroup.card_dvd_of_le hUR
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hXdvd : Nat.card (↥U ⧸ Z.subgroupOf U) ∣ 16 := by
    rw [hUcard, hcard] at hdvd
    have : Nat.card (↥U ⧸ Z.subgroupOf U) * Nat.card Z ∣ 16 * Nat.card Z := hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hZpos this
  have hX := nat_dvd16_mod5 _ hXdvd hmod
  rcases hX with h | h
  · left
    symm
    apply Subgroup.eq_of_le_of_card_ge hZU
    rw [hUcard, h]; simp
  · right
    apply Subgroup.eq_of_le_of_card_ge hUR
    rw [hcard, hUcard, h]

end Irr

end CFSG.GH74.Uniqueness.SU.SU8
