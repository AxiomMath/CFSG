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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup

variable {G : Type*} [Group G] {M : Subgroup G} {S : Type*} [Group S] (ψ : M ≃* S × S)

@[expose] def prodFactorOne : Subgroup G :=
  ((MonoidHom.inl S S).range.map ψ.symm.toMonoidHom).map M.subtype

@[expose] def prodFactorTwo : Subgroup G :=
  ((MonoidHom.inr S S).range.map ψ.symm.toMonoidHom).map M.subtype

theorem mem_prodFactorOne_iff {x : G} :
    x ∈ prodFactorOne ψ ↔ ∃ hx : x ∈ M, (ψ ⟨x, hx⟩).2 = 1 := by
  constructor
  · rintro ⟨y, ⟨z, ⟨s, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(ψ.symm (s, 1)).2, ?_⟩
    simp
  · rintro ⟨hx, h2⟩
    refine ⟨⟨x, hx⟩, ⟨ψ ⟨x, hx⟩, ⟨(ψ ⟨x, hx⟩).1, ?_⟩, ?_⟩, rfl⟩
    · rw [MonoidHom.inl_apply, ← h2]
    · simp

theorem mem_prodFactorTwo_iff {x : G} :
    x ∈ prodFactorTwo ψ ↔ ∃ hx : x ∈ M, (ψ ⟨x, hx⟩).1 = 1 := by
  constructor
  · rintro ⟨y, ⟨z, ⟨s, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(ψ.symm (1, s)).2, ?_⟩
    simp
  · rintro ⟨hx, h1⟩
    refine ⟨⟨x, hx⟩, ⟨ψ ⟨x, hx⟩, ⟨(ψ ⟨x, hx⟩).2, ?_⟩, ?_⟩, rfl⟩
    · rw [MonoidHom.inr_apply, ← h1]
    · simp

theorem prodFactorOne_le : prodFactorOne ψ ≤ M := map_subtype_le _

theorem prodFactorTwo_le : prodFactorTwo ψ ≤ M := map_subtype_le _

theorem prodFactorOne_inf_prodFactorTwo : prodFactorOne ψ ⊓ prodFactorTwo ψ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨hxM, h2⟩ := (mem_prodFactorOne_iff ψ).1 hx1
  obtain ⟨hxM', h1⟩ := (mem_prodFactorTwo_iff ψ).1 hx2
  have : ψ ⟨x, hxM⟩ = 1 := Prod.ext h1 h2
  have h3 : (⟨x, hxM⟩ : M) = 1 := by
    rw [← ψ.symm_apply_apply ⟨x, hxM⟩, this, map_one]
  exact mem_bot.2 (congrArg Subtype.val h3)

theorem prodFactorOne_le_centralizer :
    prodFactorOne ψ ≤ centralizer (prodFactorTwo ψ : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨hxM, hx2⟩ := (mem_prodFactorOne_iff ψ).1 hx
  obtain ⟨hyM, hy1⟩ := (mem_prodFactorTwo_iff ψ).1 hy
  have e : ψ (⟨y, hyM⟩ * ⟨x, hxM⟩) = ψ (⟨x, hxM⟩ * ⟨y, hyM⟩) := by
    rw [map_mul, map_mul]
    ext
    · simp [hy1]
    · simp [hx2]
  exact congrArg Subtype.val (ψ.injective e)

theorem prodFactorTwo_le_centralizer :
    prodFactorTwo ψ ≤ centralizer (prodFactorOne ψ : Set G) :=
  (le_centralizer_iff).1 (prodFactorOne_le_centralizer ψ)

theorem symm_inl_mem_prodFactorOne (s : S) : ((ψ.symm (s, 1) : M) : G) ∈ prodFactorOne ψ :=
  (mem_prodFactorOne_iff ψ).2 ⟨(ψ.symm (s, 1)).2, by simp⟩

theorem symm_inr_mem_prodFactorTwo (s : S) : ((ψ.symm (1, s) : M) : G) ∈ prodFactorTwo ψ :=
  (mem_prodFactorTwo_iff ψ).2 ⟨(ψ.symm (1, s)).2, by simp⟩

theorem exists_mul_of_mem {x : G} (hx : x ∈ M) :
    ∃ x₁ ∈ prodFactorOne ψ, ∃ x₂ ∈ prodFactorTwo ψ, x = x₁ * x₂ := by
  refine ⟨_, symm_inl_mem_prodFactorOne ψ (ψ ⟨x, hx⟩).1, _,
    symm_inr_mem_prodFactorTwo ψ (ψ ⟨x, hx⟩).2, ?_⟩
  rw [← coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta,
    MulEquiv.symm_apply_apply]

theorem prodFactorOne_sup_prodFactorTwo : prodFactorOne ψ ⊔ prodFactorTwo ψ = M := by
  refine le_antisymm (sup_le (prodFactorOne_le ψ) (prodFactorTwo_le ψ)) fun x hx => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem ψ hx
  exact mul_mem (mem_sup_left hx₁) (mem_sup_right hx₂)

theorem le_normalizer_prodFactorOne : M ≤ normalizer (prodFactorOne ψ : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ prodFactorOne ψ, g * x * g⁻¹ ∈ prodFactorOne ψ := by
    intro g hg x hx
    obtain ⟨hxM, hx2⟩ := (mem_prodFactorOne_iff ψ).1 hx
    refine (mem_prodFactorOne_iff ψ).2 ⟨mul_mem (mul_mem hg hxM) (inv_mem hg), ?_⟩
    have e : (⟨g * x * g⁻¹, mul_mem (mul_mem hg hxM) (inv_mem hg)⟩ : M) =
        ⟨g, hg⟩ * ⟨x, hxM⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    simp [hx2]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem le_normalizer_prodFactorTwo : M ≤ normalizer (prodFactorTwo ψ : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ prodFactorTwo ψ, g * x * g⁻¹ ∈ prodFactorTwo ψ := by
    intro g hg x hx
    obtain ⟨hxM, hx1⟩ := (mem_prodFactorTwo_iff ψ).1 hx
    refine (mem_prodFactorTwo_iff ψ).2 ⟨mul_mem (mul_mem hg hxM) (inv_mem hg), ?_⟩
    have e : (⟨g * x * g⁻¹, mul_mem (mul_mem hg hxM) (inv_mem hg)⟩ : M) =
        ⟨g, hg⟩ * ⟨x, hxM⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    simp [hx1]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

@[expose] noncomputable def prodFactorOneEquiv : prodFactorOne ψ ≃* S :=
  MulEquiv.ofBijective
    ((MonoidHom.fst S S).comp (ψ.toMonoidHom.comp
      (Subgroup.inclusion (prodFactorOne_le ψ))))
    ⟨fun a b hab => by
      obtain ⟨ha, ha2⟩ := (mem_prodFactorOne_iff ψ).1 a.2
      obtain ⟨hb, hb2⟩ := (mem_prodFactorOne_iff ψ).1 b.2
      have e : ψ ⟨a, ha⟩ = ψ ⟨b, hb⟩ := Prod.ext hab (by rw [ha2, hb2])
      exact Subtype.ext (congrArg (fun z : M => (z : G)) (ψ.injective e)),
    fun s => ⟨⟨_, symm_inl_mem_prodFactorOne ψ s⟩, by
      simp [Subgroup.inclusion]⟩⟩

@[expose] noncomputable def prodFactorTwoEquiv : prodFactorTwo ψ ≃* S :=
  MulEquiv.ofBijective
    ((MonoidHom.snd S S).comp (ψ.toMonoidHom.comp
      (Subgroup.inclusion (prodFactorTwo_le ψ))))
    ⟨fun a b hab => by
      obtain ⟨ha, ha1⟩ := (mem_prodFactorTwo_iff ψ).1 a.2
      obtain ⟨hb, hb1⟩ := (mem_prodFactorTwo_iff ψ).1 b.2
      have e : ψ ⟨a, ha⟩ = ψ ⟨b, hb⟩ := Prod.ext (by rw [ha1, hb1]) hab
      exact Subtype.ext (congrArg (fun z : M => (z : G)) (ψ.injective e)),
    fun s => ⟨⟨_, symm_inr_mem_prodFactorTwo ψ s⟩, by
      simp [Subgroup.inclusion]⟩⟩

theorem conj_mem_prodFactorTwo_of_swap {t : G} (ht : t ∈ normalizer (M : Set G))
    (hswap : ∀ (x y : M) (y₁ y₂ : S), (y : G) = t⁻¹ * x * t → ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {x : G} (hx : x ∈ prodFactorOne ψ) : t⁻¹ * x * t ∈ prodFactorTwo ψ := by
  obtain ⟨hxM, hx2⟩ := (mem_prodFactorOne_iff ψ).1 hx
  have hy : t⁻¹ * x * t ∈ M := by
    have := (mem_normalizer_iff.1 (inv_mem ht) x).1 hxM
    rwa [inv_inv] at this
  refine (mem_prodFactorTwo_iff ψ).2 ⟨hy, ?_⟩
  have := hswap ⟨x, hxM⟩ ⟨_, hy⟩ (ψ ⟨x, hxM⟩).1 (ψ ⟨x, hxM⟩).2 rfl (Prod.mk.eta).symm
  rw [this, hx2]

theorem conj_mem_prodFactorOne_of_swap {t : G} (ht : t ∈ normalizer (M : Set G))
    (hswap : ∀ (x y : M) (y₁ y₂ : S), (y : G) = t⁻¹ * x * t → ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {x : G} (hx : x ∈ prodFactorTwo ψ) : t⁻¹ * x * t ∈ prodFactorOne ψ := by
  obtain ⟨hxM, hx1⟩ := (mem_prodFactorTwo_iff ψ).1 hx
  have hy : t⁻¹ * x * t ∈ M := by
    have := (mem_normalizer_iff.1 (inv_mem ht) x).1 hxM
    rwa [inv_inv] at this
  refine (mem_prodFactorOne_iff ψ).2 ⟨hy, ?_⟩
  have := hswap ⟨x, hxM⟩ ⟨_, hy⟩ (ψ ⟨x, hxM⟩).1 (ψ ⟨x, hxM⟩).2 rfl (Prod.mk.eta).symm
  rw [this, hx1]

end CFSG.LocalAnalysis.EvenBN.Common
