module

import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
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

namespace CFSG.AGLEmbedding.LeviBlock

open scoped commutatorElement

variable {Q : Type} [Group Q]

theorem commutator_mem_of_mem_torus_sup {T N : Subgroup Q}
    (hTN : T ≤ Subgroup.normalizer (N : Set Q)) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {x y : Q} (hx : x ∈ T ⊔ N) (hy : y ∈ T ⊔ N) : ⁅x, y⁆ ∈ N := by
  have hx' : x ∈ ((T ⊔ N : Subgroup Q) : Set Q) := hx
  have hy' : y ∈ ((T ⊔ N : Subgroup Q) : Set Q) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hx' hy'
  obtain ⟨t₁, ht₁, n₁, hn₁, rfl⟩ := hx'
  obtain ⟨t₂, ht₂, n₂, hn₂, rfl⟩ := hy'
  have hc : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun t ht n hn =>
    (Subgroup.mem_normalizer_iff.1 (hTN ht) n).1 hn
  have h1 : t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = 1 := by
    rw [hTc t₁ ht₁ t₂ ht₂]
    group
  have e : ⁅t₁ * n₁, t₂ * n₂⁆ = (t₁ * n₁ * t₁⁻¹) * ((t₁ * t₂) * (n₂ * n₁⁻¹) * (t₁ * t₂)⁻¹) *
      (t₁ * t₂ * t₁⁻¹ * t₂⁻¹) * (t₂ * n₂⁻¹ * t₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, h1, mul_one]
  exact mul_mem (mul_mem (hc t₁ ht₁ n₁ hn₁)
    (hc _ (mul_mem ht₁ ht₂) _ (mul_mem hn₂ (inv_mem hn₁)))) (hc t₂ ht₂ _ (inv_mem hn₂))

theorem isPGroup_ker_oneBlock (U : Subgroup Q) [U.Normal] (hU : IsPGroup 2 U) :
    IsPGroup 2 (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).ker := by
  rintro ⟨x, hx⟩
  have hxU : x ∈ U := by
    have h := congrFun (MonoidHom.mem_ker.1 hx) 0
    rwa [MonoidHom.pi_apply, Pi.one_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := hU ⟨x, hxU⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem pi_le_range_oneBlock (U Λ : Subgroup Q) [U.Normal] :
    Subgroup.pi Set.univ (fun _ : Fin 1 => Λ.map (QuotientGroup.mk' U)) ≤
      (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range := by
  intro g _
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective U (g 0)
  exact ⟨x, funext fun j => by rw [Fin.fin_one_eq_zero j, MonoidHom.pi_apply, hx]⟩

theorem commutator_range_oneBlock_le (U Λ : Subgroup Q) [U.Normal]
    (hc : ∀ a b : Q, ⁅a, b⁆ ∈ Λ ⊔ U) :
    ⁅(MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range,
        (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range⁆ ≤
      Subgroup.pi Set.univ (fun _ : Fin 1 => Λ.map (QuotientGroup.mk' U)) := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ j -
  rw [← map_commutatorElement, MonoidHom.pi_apply]
  have h : ⁅a, b⁆ ∈ ((Λ ⊔ U : Subgroup Q) : Set Q) := hc a b
  rw [Subgroup.mul_normal] at h
  obtain ⟨l, hl, u, hu, he⟩ := h
  refine ⟨l, hl, ?_⟩
  rw [← he, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  simpa using hu

theorem nonempty_mulEquiv_oneBlock (U Λ : Subgroup Q) [U.Normal] (h : Λ ⊓ U = ⊥) :
    Nonempty (↥Λ ≃* ↥(Λ.map (QuotientGroup.mk' U))) := by
  refine ⟨MulEquiv.ofBijective ((QuotientGroup.mk' U).subgroupMap Λ)
    ⟨fun a b hab => ?_, (QuotientGroup.mk' U).subgroupMap_surjective Λ⟩⟩
  have h1 : QuotientGroup.mk' U (a : Q) = QuotientGroup.mk' U (b : Q) := congrArg Subtype.val hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 : (a : Q)⁻¹ * b ∈ Λ ⊓ U := ⟨Λ.mul_mem (Λ.inv_mem a.2) b.2, h1⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact Subtype.ext h2

theorem inf_eq_bot_of_simple_of_isPGroup {Λ U : Subgroup Q} [Finite Λ] [IsSimpleGroup Λ]
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (hΛU : Λ ≤ Subgroup.normalizer (U : Set Q))
    (hU : IsPGroup 2 U) : Λ ⊓ U = ⊥ := by
  have hN : (U.subgroupOf Λ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.1 (hΛU g.2) n).1 hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.subgroupOf Λ) with h | h
  · exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h).symm
  · exfalso
    refine not_isPGroup_two_of_simple hnc fun g => ?_
    have hg : (g : Q) ∈ U := Subgroup.mem_subgroupOf.1 (h ▸ Subgroup.mem_top g)
    obtain ⟨k, hk⟩ := hU ⟨g, hg⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem card_quotient_center_of_eq_bot {S : Type} [Group S] (h : Subgroup.center S = ⊥) :
    Nat.card (S ⧸ Subgroup.center S) = Nat.card S := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S), h, Subgroup.card_bot,
    mul_one]

end CFSG.AGLEmbedding.LeviBlock
