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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup
open scoped commutatorElement

theorem commutator_le_closure_of_central {G : Type*} [Group G] {Γ Z : Subgroup G} {a b : G}
    (hZ : ∀ z ∈ Z, ∀ g ∈ Γ, z * g = g * z) (hZΓ : Z ≤ Γ) (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hΓ : Γ ≤ Z ⊔ Subgroup.closure {a, b}) (hc : a * b * a⁻¹ * b⁻¹ ∈ Z) :
    ⁅Γ, Γ⁆ ≤ Subgroup.closure {a * b * a⁻¹ * b⁻¹} := by
  suffices main : ∀ C : Subgroup G, a * b * a⁻¹ * b⁻¹ ∈ C → C ≤ Z → ⁅Γ, Γ⁆ ≤ C from
    main _ (Subgroup.subset_closure rfl) ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hc))
  intro C hcC hCZ
  have hconj : ∀ u ∈ C, ∀ g ∈ Γ, g * u * g⁻¹ = u := fun u hu g hg => by
    rw [← hZ u (hCZ hu) g hg]; group
  have hgen : Γ = Subgroup.closure ((Z : Set G) ∪ {a, b}) := by
    refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.closure_union, Subgroup.closure_eq]
      exact hΓ
    · rintro x (hx | hx | hx)
      · exact hZΓ hx
      · rw [hx]; exact ha
      · rw [Set.mem_singleton_iff.1 hx]; exact hb
  have hkΓ : ∀ x ∈ (Z : Set G) ∪ {a, b}, x ∈ Γ := fun x hx => hgen ▸ Subgroup.subset_closure hx
  have key : ∀ x y : G, x ∈ Subgroup.closure ((Z : Set G) ∪ {a, b}) →
      y ∈ Subgroup.closure ((Z : Set G) ∪ {a, b}) → x * y * x⁻¹ * y⁻¹ ∈ C := by
    intro x y hx hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y * x⁻¹ * y⁻¹ ∈ C) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ hx hy
    ·
      intro x y hx hy
      have hxΓ : x ∈ Γ := hkΓ x hx
      have hyΓ : y ∈ Γ := hkΓ y hy
      rcases hx with hx | hx
      · rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [hZ x hx y hyΓ]; group]
        exact one_mem _
      rcases hy with hy | hy
      · rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [← hZ y hy x hxΓ]; group]
        exact one_mem _
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · rw [hx, hy]
          rw [show a * a * a⁻¹ * a⁻¹ = 1 by group]
          exact one_mem _
        · rw [hx, Set.mem_singleton_iff.1 hy]
          exact hcC
      · rw [Set.mem_singleton_iff.1 hx]
        rcases hy with hy | hy
        · rw [hy, show b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ by group]
          exact inv_mem hcC
        · rw [Set.mem_singleton_iff.1 hy]
          rw [show b * b * b⁻¹ * b⁻¹ = 1 by group]
          exact one_mem _
    · intro x hx
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz h₁ h₂
      have hxΓ : x ∈ Γ := hgen ▸ hx
      have e : x * y * z * (x * y)⁻¹ * z⁻¹ =
          (x * (y * z * y⁻¹ * z⁻¹) * x⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group
      rw [e, hconj _ h₂ x hxΓ]
      exact mul_mem h₂ h₁
    · intro y z x hy hz hx h₁ h₂
      have hyΓ : y ∈ Γ := hgen ▸ hy
      have e : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
      rw [e, hconj _ h₂ y hyΓ]
      exact mul_mem h₁ h₂
    · intro x y hx hy h
      have hxΓ : x ∈ Γ := hgen ▸ hx
      have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e, hconj _ (inv_mem h) x⁻¹ (inv_mem hxΓ)]
      exact inv_mem h
    · intro x y hx hy h
      have hyΓ : y ∈ Γ := hgen ▸ hy
      have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
      rw [e, hconj _ (inv_mem h) y⁻¹ (inv_mem hyΓ)]
      exact inv_mem h
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  rw [hgen] at hg hh
  exact key g h hg hh

theorem card_eq_card_inf_ker_mul_card_map {Γ Γ' : Type*} [Group Γ] [Group Γ'] (φ : Γ →* Γ')
    (S : Subgroup Γ) :
    Nat.card S = Nat.card (S ⊓ φ.ker : Subgroup Γ) * Nat.card (S.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp S.subtype)
  have hker : (φ.comp S.subtype).ker.map S.subtype = S ⊓ φ.ker := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.2 ⟨s.2, hs⟩
    · intro hx
      obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.1 hx
      exact ⟨⟨x, hxS⟩, hxk, rfl⟩
  have hrange : (φ.comp S.subtype).range = S.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, hrange, ← hker, Subgroup.card_map_of_injective S.subtype_injective]

theorem card_eq_two_mul_card_inf_centralizer {G : Type*} [Group G] [Finite G] (M' : Subgroup G)
    (z z₀ : G) (hzz : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ m ∈ M', m * z = z * m)
    (hcomm : ∀ m ∈ M', m * z₀ * m⁻¹ * z₀⁻¹ ∈ zpowers z) {m₀ : G} (hm₀ : m₀ ∈ M')
    (hm₀z : m₀ * z₀ * m₀⁻¹ * z₀⁻¹ = z) :
    Nat.card M' = 2 * Nat.card (M' ⊓ centralizer ({z₀} : Set G) : Subgroup G) := by
  have hconj : ∀ m ∈ M', ∀ w ∈ zpowers z, m * w * m⁻¹ = w := by
    intro m hm w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [(Commute.zpow_right (hzc m hm) k).eq]
    group
  have hcz : ∀ w₁ ∈ zpowers z, ∀ w₂ ∈ zpowers z, w₁ * w₂ = w₂ * w₁ := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 h₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 h₂
    exact (Commute.zpow_zpow_self z i j).eq
  let φ : M' →* ↥(zpowers z) :=
    MonoidHom.mk' (fun m => ⟨m * z₀ * m⁻¹ * z₀⁻¹, hcomm m m.2⟩) fun a b => by
      refine Subtype.ext ?_
      show (a : G) * b * z₀ * ((a : G) * b)⁻¹ * z₀⁻¹ =
        ((a : G) * z₀ * (a : G)⁻¹ * z₀⁻¹) * ((b : G) * z₀ * (b : G)⁻¹ * z₀⁻¹)
      have e : (a : G) * b * z₀ * ((a : G) * b)⁻¹ * z₀⁻¹ =
          (a : G) * ((b : G) * z₀ * (b : G)⁻¹ * z₀⁻¹) * (a : G)⁻¹ *
            ((a : G) * z₀ * (a : G)⁻¹ * z₀⁻¹) := by group
      rw [e, hconj a a.2 _ (hcomm b b.2)]
      exact hcz _ (hcomm b b.2) _ (hcomm a a.2)
  have hker : φ.ker.map M'.subtype = M' ⊓ centralizer ({z₀} : Set G) := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine Subgroup.mem_inf.2 ⟨m.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.1 hh]
      have h1 : (m : G) * z₀ * (m : G)⁻¹ * z₀⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
      exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
    · intro hx
      obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxM⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      have h1 : z₀ * x = x * z₀ := Subgroup.mem_centralizer_iff.1 hxc z₀ (Set.mem_singleton z₀)
      show x * z₀ * x⁻¹ * z₀⁻¹ = 1
      rw [← h1]
      group
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    refine ⟨(⟨m₀, hm₀⟩ : M') ^ k, ?_⟩
    have h1 : φ ⟨m₀, hm₀⟩ = ⟨z, Subgroup.mem_zpowers z⟩ := Subtype.ext hm₀z
    rw [map_zpow, h1]
    exact Subtype.ext (by simp)
  have h2 : Nat.card φ.range = 2 := by
    rw [hrange, Subgroup.card_top, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have h := Subgroup.card_ker_mul_card_range φ
  rw [h2] at h
  have hk : Nat.card φ.ker = Nat.card (M' ⊓ centralizer ({z₀} : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective M'.subtype_injective]
  rw [← h, hk, mul_comm]

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
