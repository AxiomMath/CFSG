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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup
open scoped commutatorElement

section Unique

variable {X L₁ L₂ : Type} [Group X] [Group L₁] [Group L₂]

@[expose] def fibre (π₁ : L₁ →* X) (π₂ : L₂ →* X) : Subgroup (L₁ × L₂) :=
  (π₁.comp (MonoidHom.fst L₁ L₂)).eqLocus (π₂.comp (MonoidHom.snd L₁ L₂))

theorem mem_fibre {π₁ : L₁ →* X} {π₂ : L₂ →* X} {p : L₁ × L₂} :
    p ∈ fibre π₁ π₂ ↔ π₁ p.1 = π₂ p.2 := Iff.rfl

theorem commutator_le_self {G : Type} [Group G] (F : Subgroup G) : ⁅F, F⁆ ≤ F :=
  commutator_le.2 fun _ ha _ hb => F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha))
    (F.inv_mem hb)

theorem commutator_mul_central {G : Type} [Group G] {k k' d d' : G}
    (hk : ∀ g, k * g = g * k) (hk' : ∀ g, k' * g = g * k') :
    ⁅k * d, k' * d'⁆ = ⁅d, d'⁆ := by
  have hconj : ∀ (c x : G), (∀ g, c * g = g * c) → c * x * c⁻¹ = x := by
    intro c x hc
    rw [hc x, mul_inv_cancel_right]
  have hcomm : ∀ (c x : G), (∀ g, c * g = g * c) → ⁅c, x⁆ = 1 := fun c x hc =>
    commutatorElement_eq_one_iff_mul_comm.2 (hc x)
  have hcomm' : ∀ (c x : G), (∀ g, c * g = g * c) → ⁅x, c⁆ = 1 := fun c x hc =>
    commutatorElement_eq_one_iff_mul_comm.2 (hc x).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hcomm k _ hk, mul_one, hconj k _ hk,
    commutatorElement_mul_right_eq_mul_conj, hcomm' k' _ hk', one_mul, hconj k' _ hk']

theorem exists_mulEquiv_of_double_covers [Finite L₁] [Finite L₂]
    (hX : Group.IsPerfect X) (hL₁ : Group.IsPerfect L₁) (hL₂ : Group.IsPerfect L₂)
    (π₁ : L₁ →* X) (π₂ : L₂ →* X) (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (hk₁ : Nat.card π₁.ker = 2) (hk₂ : Nat.card π₂.ker = 2)
    (hz₁ : π₁.ker ≤ center L₁) (hz₂ : π₂.ker ≤ center L₂)
    (hbound : ∀ (F : Type) [Group F] [Finite F], Group.IsPerfect F → ∀ (ρ : F →* X),
      Function.Surjective ρ → ρ.ker ≤ center F → (∀ k ∈ ρ.ker, k ^ 2 = 1) →
        Nat.card ρ.ker ≤ 2) :
    ∃ e : L₁ ≃* L₂, ∀ a, π₂ (e a) = π₁ a := by
  set F := fibre π₁ π₂ with hF
  set D : Subgroup (L₁ × L₂) := ⁅F, F⁆ with hD
  have hDF : D ≤ F := commutator_le_self F
  have lift : ∀ x : X, ∃ p ∈ F, π₁ p.1 = x := fun x => by
    obtain ⟨a, rfl⟩ := h₁ x
    obtain ⟨b, hb⟩ := h₂ (π₁ a)
    exact ⟨(a, b), hb.symm, rfl⟩
  have lift₁ : ∀ a : L₁, ∃ p ∈ F, p.1 = a := fun a => by
    obtain ⟨b, hb⟩ := h₂ (π₁ a)
    exact ⟨(a, b), hb.symm, rfl⟩
  have lift₂ : ∀ b : L₂, ∃ p ∈ F, p.2 = b := fun b => by
    obtain ⟨a, ha⟩ := h₁ (π₂ b)
    exact ⟨(a, b), ha, rfl⟩
  let ρ : D →* X := π₁.comp ((MonoidHom.fst L₁ L₂).comp D.subtype)
  have hcomm_fst : ∀ p q : L₁ × L₂, ⁅p, q⁆.1 = ⁅p.1, q.1⁆ := fun p q => by
    simp [commutatorElement_def]
  have hcomm_snd : ∀ p q : L₁ × L₂, ⁅p, q⁆.2 = ⁅p.2, q.2⁆ := fun p q => by
    simp [commutatorElement_def]
  have hρ : Function.Surjective ρ := by
    have h1 : (⊤ : Subgroup X) ≤ ρ.range := by
      have : (⊤ : Subgroup X) = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
        (Group.isPerfect_def.1 hX).symm
      rw [this]
      refine commutator_le.2 fun x _ y _ => ?_
      obtain ⟨p, hp, rfl⟩ := lift x
      obtain ⟨q, hq, rfl⟩ := lift y
      exact ⟨⟨⁅p, q⁆, commutator_mem_commutator hp hq⟩, by
        show π₁ ⁅p, q⁆.1 = _
        rw [hcomm_fst, map_commutatorElement]⟩
    intro x
    exact MonoidHom.mem_range.1 (h1 (mem_top x))
  have central : ∀ k ∈ F, π₁ k.1 = 1 → ∀ g : L₁ × L₂, k * g = g * k := fun k hk h1 g => by
    have h2 : π₂ k.2 = 1 := by rw [← mem_fibre.1 hk, h1]
    exact Prod.ext (mem_center_iff.1 (hz₁ h1) g.1).symm (mem_center_iff.1 (hz₂ h2) g.2).symm
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (commutator_le_self D) ?_
    rw [hD]
    have dec : ∀ f ∈ F, ∃ k ∈ F, π₁ k.1 = 1 ∧ ∃ d ∈ D, f = k * d := by
      intro f hf
      obtain ⟨d, hd⟩ := hρ (π₁ f.1)
      refine ⟨f * (d : L₁ × L₂)⁻¹, F.mul_mem hf (F.inv_mem (hDF d.2)), ?_, d, d.2, by group⟩
      show π₁ (f.1 * (d : L₁ × L₂).1⁻¹) = 1
      rw [map_mul, map_inv, show π₁ (d : L₁ × L₂).1 = π₁ f.1 from hd, mul_inv_cancel]
    refine commutator_le.2 fun f hf f' hf' => ?_
    obtain ⟨k, hk, hk1, d, hd, rfl⟩ := dec f hf
    obtain ⟨k', hk', hk1', d', hd', rfl⟩ := dec f' hf'
    rw [commutator_mul_central (central k hk hk1) (central k' hk' hk1')]
    exact commutator_mem_commutator hd hd'
  have hperfD : Group.IsPerfect ↥D := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_injective D.subtype_injective
    rw [show _root_.commutator ↥D = ⁅(⊤ : Subgroup ↥D), ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top, Subgroup.range_subtype, hDperf]
  have hker : ∀ d : D, d ∈ ρ.ker → d.1.1 ∈ π₁.ker ∧ d.1.2 ∈ π₂.ker := fun d hd => by
    have h1 : π₁ d.1.1 = 1 := hd
    exact ⟨h1, (mem_fibre.1 (hDF d.2)).symm.trans h1⟩
  have hcard_ker : Nat.card ρ.ker ≤ 2 := by
    refine hbound ↥D hperfD ρ hρ (fun d hd => ?_) fun d hd => ?_
    · rw [mem_center_iff]
      intro e
      exact Subtype.ext (central d.1 (hDF d.2) hd e.1).symm
    · obtain ⟨h1, h2'⟩ := hker d hd
      have e1 : ∀ g : π₁.ker, g ^ 2 = 1 := fun g => by
        rw [← hk₁]; exact pow_card_eq_one'
      have e2 : ∀ g : π₂.ker, g ^ 2 = 1 := fun g => by
        rw [← hk₂]; exact pow_card_eq_one'
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val (e1 ⟨d.1.1, h1⟩)
      · exact congrArg Subtype.val (e2 ⟨d.1.2, h2'⟩)
  have cardL₁ : Nat.card L₁ = Nat.card X * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π₁.ker, hk₁,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π₁ h₁).toEquiv]
  have cardL₂ : Nat.card L₂ = Nat.card X * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π₂.ker, hk₂,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π₂ h₂).toEquiv]
  have cardD : Nat.card D ≤ Nat.card X * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]
    exact Nat.mul_le_mul_left _ hcard_ker
  let p₁ : D →* L₁ := (MonoidHom.fst L₁ L₂).comp D.subtype
  let p₂ : D →* L₂ := (MonoidHom.snd L₁ L₂).comp D.subtype
  have hp₁ : Function.Surjective p₁ := by
    have h1 : (⊤ : Subgroup L₁) ≤ p₁.range := by
      have : (⊤ : Subgroup L₁) = ⁅(⊤ : Subgroup L₁), (⊤ : Subgroup L₁)⁆ :=
        (Group.isPerfect_def.1 hL₁).symm
      rw [this]
      refine commutator_le.2 fun a _ b _ => ?_
      obtain ⟨p, hp, rfl⟩ := lift₁ a
      obtain ⟨q, hq, rfl⟩ := lift₁ b
      exact ⟨⟨⁅p, q⁆, commutator_mem_commutator hp hq⟩, by
        show ⁅p, q⁆.1 = _
        rw [hcomm_fst]⟩
    intro a
    exact MonoidHom.mem_range.1 (h1 (mem_top a))
  have hp₂ : Function.Surjective p₂ := by
    have h1 : (⊤ : Subgroup L₂) ≤ p₂.range := by
      have : (⊤ : Subgroup L₂) = ⁅(⊤ : Subgroup L₂), (⊤ : Subgroup L₂)⁆ :=
        (Group.isPerfect_def.1 hL₂).symm
      rw [this]
      refine commutator_le.2 fun a _ b _ => ?_
      obtain ⟨p, hp, rfl⟩ := lift₂ a
      obtain ⟨q, hq, rfl⟩ := lift₂ b
      exact ⟨⟨⁅p, q⁆, commutator_mem_commutator hp hq⟩, by
        show ⁅p, q⁆.2 = _
        rw [hcomm_snd]⟩
    intro a
    exact MonoidHom.mem_range.1 (h1 (mem_top a))
  have hb₁ : Function.Bijective p₁ := hp₁.bijective_of_nat_card_le (by omega)
  have hb₂ : Function.Bijective p₂ := hp₂.bijective_of_nat_card_le (by omega)
  refine ⟨(MulEquiv.ofBijective p₁ hb₁).symm.trans (MulEquiv.ofBijective p₂ hb₂), fun a => ?_⟩
  have hd : p₁ ((MulEquiv.ofBijective p₁ hb₁).symm a) = a :=
    MulEquiv.apply_symm_apply (MulEquiv.ofBijective p₁ hb₁) a
  set d := (MulEquiv.ofBijective p₁ hb₁).symm a
  show π₂ (p₂ d) = π₁ a
  rw [← hd]
  exact (mem_fibre.1 (hDF d.2)).symm

end Unique

end CFSG.EvenSporadicStandard.TwoCo1
