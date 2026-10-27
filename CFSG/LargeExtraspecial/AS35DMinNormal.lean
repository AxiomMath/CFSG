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

namespace CFSG.LargeExtraspecial.Asc77

open Subgroup

variable {G : Type} [Group G]

@[expose] def subConj (K : Subgroup G) (g : G) : Subgroup G where
  carrier := {y | g⁻¹ * y * g ∈ K}
  one_mem' := by
    change g⁻¹ * 1 * g ∈ K
    rw [mul_one, inv_mul_cancel]
    exact K.one_mem
  mul_mem' := by
    intro a b ha hb
    change g⁻¹ * (a * b) * g ∈ K
    rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
    exact K.mul_mem ha hb
  inv_mem' := by
    intro a ha
    change g⁻¹ * a⁻¹ * g ∈ K
    rw [show g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ by group]
    exact K.inv_mem ha

theorem mem_subConj {K : Subgroup G} {g y : G} : y ∈ subConj K g ↔ g⁻¹ * y * g ∈ K := Iff.rfl

theorem conj_mem_subConj {K : Subgroup G} {g k : G} (hk : k ∈ K) : g * k * g⁻¹ ∈ subConj K g := by
  rw [mem_subConj, show g⁻¹ * (g * k * g⁻¹) * g = k by group]
  exact hk

theorem subConj_mul (K : Subgroup G) (g h : G) : subConj (subConj K h) g = subConj K (g * h) := by
  ext y
  simp only [mem_subConj, mul_inv_rev, mul_assoc]

theorem subConj_one (K : Subgroup G) : subConj K 1 = K := by
  ext y
  simp [mem_subConj]

theorem subConj_le_of_normalizes {K L : Subgroup G} {g : G} (hLg : ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hKL : K ≤ L) : subConj K g ≤ L := by
  intro y hy
  have := hLg _ (hKL (mem_subConj.mp hy))
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this

theorem subConj_eq_bot_iff {K : Subgroup G} {g : G} : subConj K g = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro k hk
    have := conj_mem_subConj (g := g) hk
    rw [h, mem_bot] at this
    rw [mem_bot]
    calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  · rintro rfl
    rw [eq_bot_iff]
    intro y hy
    rw [mem_subConj, mem_bot] at hy
    rw [mem_bot]
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [hy]; group

theorem conj_mem_map_of_characteristic {N : Subgroup G} (C : Subgroup N) [hC : C.Characteristic]
    {x : G} (hx : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hx' : ∀ n ∈ N, x⁻¹ * n * x ∈ N) {y : G}
    (hy : y ∈ C.map N.subtype) : x * y * x⁻¹ ∈ C.map N.subtype := by
  obtain ⟨c, hc, rfl⟩ := hy
  let φ : N ≃* N :=
    { toFun := fun n => ⟨x * n * x⁻¹, hx n n.2⟩
      invFun := fun n => ⟨x⁻¹ * n * x, hx' n n.2⟩
      left_inv := fun n => Subtype.ext (by
        change x⁻¹ * (x * n * x⁻¹) * x = n
        group)
      right_inv := fun n => Subtype.ext (by
        change x * (x⁻¹ * n * x) * x⁻¹ = n
        group)
      map_mul' := fun a b => Subtype.ext (by
        change x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
        group) }
  have hmap := (characteristic_iff_map_eq.mp hC) φ
  refine ⟨φ c, ?_, rfl⟩
  rw [← hmap]
  exact ⟨c, hc, rfl⟩

theorem normal_conj_mem {L : Subgroup G} (hL : L.Normal) (x : G) :
    (∀ n ∈ L, x * n * x⁻¹ ∈ L) ∧ ∀ n ∈ L, x⁻¹ * n * x ∈ L :=
  ⟨fun n hn => hL.conj_mem n hn x, fun n hn => by
    have := hL.conj_mem n hn x⁻¹
    rwa [inv_inv] at this⟩

@[expose] def IsMinNormalIn (L K : Subgroup G) : Prop :=
  K ≤ L ∧ (∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) ∧ K ≠ ⊥ ∧
    ∀ K' : Subgroup G, K' ≤ K → (∀ l ∈ L, ∀ k ∈ K', l * k * l⁻¹ ∈ K') → K' ≠ ⊥ → K' = K

theorem exists_isMinNormalIn [Finite G] {L : Subgroup G} (hL : L ≠ ⊥) :
    ∃ K, IsMinNormalIn L K := by
  let 𝒦 : Set (Subgroup G) := {K | K ≤ L ∧ (∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) ∧ K ≠ ⊥}
  have hL𝒦 : L ∈ 𝒦 := ⟨le_rfl, fun l hl k hk => L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), hL⟩
  obtain ⟨K, ⟨hKL, hKn, hK1⟩, hKmin⟩ := (Set.toFinite 𝒦).exists_minimal ⟨L, hL𝒦⟩
  exact ⟨K, hKL, hKn, hK1, fun K' hle hn hne =>
    le_antisymm hle (hKmin ⟨hle.trans hKL, hn, hne⟩ hle)⟩

namespace IsMinNormalIn

variable {L K K' : Subgroup G}

theorem subConj (hLn : L.Normal) (hK : IsMinNormalIn L K) (g : G) :
    IsMinNormalIn L (Asc77.subConj K g) := by
  obtain ⟨hKL, hKn, hK1, hKmin⟩ := hK
  have hnorm : ∀ {K₀ : Subgroup G} {h : G}, (∀ l ∈ L, ∀ k ∈ K₀, l * k * l⁻¹ ∈ K₀) →
      ∀ l ∈ L, ∀ k ∈ Asc77.subConj K₀ h, l * k * l⁻¹ ∈ Asc77.subConj K₀ h := by
    intro K₀ h hK₀ l hl k hk
    rw [mem_subConj] at hk ⊢
    have hl' : h⁻¹ * l * h ∈ L := (normal_conj_mem hLn h).2 l hl
    have := hK₀ _ hl' _ hk
    rwa [show h⁻¹ * l * h * (h⁻¹ * k * h) * (h⁻¹ * l * h)⁻¹ = h⁻¹ * (l * k * l⁻¹) * h by
      group] at this
  refine ⟨subConj_le_of_normalizes (normal_conj_mem hLn g).1 hKL, hnorm hKn,
    fun h => hK1 (subConj_eq_bot_iff.mp h), fun K₁ hle hn hne => ?_⟩
  have h1 : Asc77.subConj K₁ g⁻¹ ≤ K := by
    intro y hy
    have := hle (mem_subConj.mp hy)
    rw [mem_subConj] at this
    rwa [show g⁻¹ * (g⁻¹⁻¹ * y * g⁻¹) * g = y by group] at this
  have h2 := hKmin _ h1 (hnorm hn) (fun h => hne (subConj_eq_bot_iff.mp h))
  rw [← h2, subConj_mul, mul_inv_cancel, subConj_one]

theorem inf_eq_bot (hK : IsMinNormalIn L K) (hK' : IsMinNormalIn L K') (hne : K ≠ K') :
    K ⊓ K' = ⊥ := by
  by_contra h
  have hn : ∀ l ∈ L, ∀ k ∈ K ⊓ K', l * k * l⁻¹ ∈ K ⊓ K' := fun l hl k hk =>
    mem_inf.mpr ⟨hK.2.1 l hl k (mem_inf.mp hk).1, hK'.2.1 l hl k (mem_inf.mp hk).2⟩
  have h1 := hK.2.2.2 _ inf_le_left hn h
  have h2 : K ≤ K' := h1 ▸ inf_le_right
  exact hne (hK'.2.2.2 K h2 hK.2.1 hK.2.2.1)

theorem commute (hK : IsMinNormalIn L K) (hK' : IsMinNormalIn L K') (hne : K ≠ K') {a b : G}
    (ha : a ∈ K) (hb : b ∈ K') : a * b = b * a := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ K ⊓ K' := by
    refine mem_inf.mpr ⟨?_, K'.mul_mem (hK'.2.1 a (hK.1 ha) b hb) (K'.inv_mem hb)⟩
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact K.mul_mem ha (hK.2.1 b (hK'.1 hb) _ (K.inv_mem ha))
  rw [hK.inf_eq_bot hK' hne, mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

end IsMinNormalIn

end CFSG.LargeExtraspecial.Asc77
