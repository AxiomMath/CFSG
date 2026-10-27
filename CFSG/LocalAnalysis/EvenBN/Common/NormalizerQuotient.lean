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

namespace CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

open Subgroup

variable {G : Type*} [Group G] (A : Subgroup G)

abbrev Bar : Type _ := ↥(normalizer (A : Set G)) ⧸ A.subgroupOf (normalizer (A : Set G))

abbrev proj : normalizer (A : Set G) →* Bar A := QuotientGroup.mk' _

variable {A}

@[expose] def bar (A X : Subgroup G) : Subgroup (Bar A) :=
  (X.subgroupOf (normalizer (A : Set G))).map (proj A)

@[expose] def lift (Y : Subgroup (Bar A)) : Subgroup G :=
  (Y.comap (proj A)).map (normalizer (A : Set G)).subtype

theorem proj_surjective : Function.Surjective (proj A) := QuotientGroup.mk'_surjective _

theorem proj_eq_proj_iff {x y : normalizer (A : Set G)} :
    proj A x = proj A y ↔ (x : G)⁻¹ * y ∈ A := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  simp

theorem proj_eq_one_iff {x : normalizer (A : Set G)} : proj A x = 1 ↔ (x : G) ∈ A := by
  rw [← map_one (proj A), proj_eq_proj_iff]
  simp

theorem mem_bar_iff {X : Subgroup G} (hAX : A ≤ X) (x : normalizer (A : Set G)) :
    proj A x ∈ bar A X ↔ (x : G) ∈ X := by
  constructor
  · rintro ⟨y, hy, e⟩
    have h1 := proj_eq_proj_iff.1 e
    have hx : (x : G) = y * ((y : G)⁻¹ * x) := by group
    rw [hx]
    exact mul_mem (mem_subgroupOf.1 hy) (hAX h1)
  · exact fun hx => ⟨x, mem_subgroupOf.2 hx, rfl⟩

theorem mem_lift_iff {Y : Subgroup (Bar A)} {g : G} :
    g ∈ lift Y ↔ ∃ hg : g ∈ normalizer (A : Set G), proj A ⟨g, hg⟩ ∈ Y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hY⟩
    exact ⟨⟨g, hg⟩, hY, rfl⟩

theorem lift_le_normalizer (Y : Subgroup (Bar A)) : lift Y ≤ normalizer (A : Set G) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem le_lift (Y : Subgroup (Bar A)) : A ≤ lift Y := fun a ha =>
  mem_lift_iff.2 ⟨le_normalizer ha, by rw [proj_eq_one_iff.2 ha]; exact one_mem _⟩

theorem proj_mem_of_mem_lift {Y : Subgroup (Bar A)} {x : normalizer (A : Set G)}
    (hx : (x : G) ∈ lift Y) : proj A x ∈ Y := by
  obtain ⟨_, hY⟩ := mem_lift_iff.1 hx
  exact hY

theorem bar_lift (Y : Subgroup (Bar A)) : bar A (lift Y) = Y := by
  ext y
  obtain ⟨x, rfl⟩ := proj_surjective y
  rw [mem_bar_iff (le_lift Y)]
  exact ⟨proj_mem_of_mem_lift, fun h => mem_lift_iff.2 ⟨x.2, h⟩⟩

theorem lift_bar {X : Subgroup G} (hAX : A ≤ X) (hXN : X ≤ normalizer (A : Set G)) :
    lift (bar A X) = X := by
  ext g
  rw [mem_lift_iff]
  constructor
  · rintro ⟨hg, hY⟩
    exact (mem_bar_iff hAX ⟨g, hg⟩).1 hY
  · intro hg
    exact ⟨hXN hg, (mem_bar_iff hAX ⟨g, hXN hg⟩).2 hg⟩

theorem bar_mono {X X' : Subgroup G} (h : X ≤ X') : bar A X ≤ bar A X' :=
  map_mono fun _ hx => h hx

theorem lift_mono {Y Y' : Subgroup (Bar A)} (h : Y ≤ Y') : lift Y ≤ lift Y' :=
  map_mono (comap_mono h)

theorem mem_lift_of_proj_mem {Y : Subgroup (Bar A)} {x : normalizer (A : Set G)}
    (hx : proj A x ∈ Y) : (x : G) ∈ lift Y :=
  mem_lift_iff.2 ⟨x.2, hx⟩

theorem proj_mem_bar {X : Subgroup G} {x : normalizer (A : Set G)} (hx : (x : G) ∈ X) :
    proj A x ∈ bar A X :=
  ⟨x, mem_subgroupOf.2 hx, rfl⟩

theorem bar_le_normalizer_bar [Finite G] {X Y : Subgroup G} (hAY : A ≤ Y)
    (hXY : X ≤ normalizer (Y : Set G)) : bar A X ≤ normalizer (bar A Y : Set (Bar A)) := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_normalizer_fintype fun y hy => ?_
  rw [SetLike.mem_coe] at hy ⊢
  obtain ⟨y₀, rfl⟩ := proj_surjective y
  have hy₀ := (mem_bar_iff hAY y₀).1 hy
  rw [← map_inv, ← map_mul, ← map_mul, mem_bar_iff hAY]
  simp only [coe_mul, coe_inv]
  exact (mem_normalizer_iff.1 (hXY (mem_subgroupOf.1 hx)) _).1 hy₀


theorem card_bar_mul [Finite G] {X : Subgroup G} (hAX : A ≤ X)
    (hXN : X ≤ normalizer (A : Set G)) : Nat.card (bar A X) * Nat.card A = Nat.card X := by
  set X' := X.subgroupOf (normalizer (A : Set G)) with hX'
  set φ : X' →* Bar A := (proj A).comp X'.subtype with hφ
  have hrange : (φ.range : Set (Bar A)) = bar A X := by
    ext y
    simp only [MonoidHom.coe_range, Set.mem_range, SetLike.mem_coe, hφ, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype, bar, mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card A := by
    refine Nat.card_congr ⟨fun k => ⟨k.1.1.1, ?_⟩, fun a => ⟨⟨⟨a.1, le_normalizer a.2⟩,
      mem_subgroupOf.2 (hAX a.2)⟩, ?_⟩, fun k => ?_, fun a => ?_⟩
    · have h0 : proj A (k : X').1 = 1 := MonoidHom.mem_ker.1 k.2
      exact proj_eq_one_iff.1 h0
    · exact MonoidHom.mem_ker.2 (proj_eq_one_iff.2 a.2)
    · rfl
    · rfl
  have hrange' : φ.range = bar A X := SetLike.coe_injective hrange
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange', hker] at h1
  rw [← Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv, ← h1, mul_comm]

theorem card_lift [Finite G] (Y : Subgroup (Bar A)) :
    Nat.card (lift Y) = Nat.card Y * Nat.card A := by
  have := card_bar_mul (le_lift Y) (lift_le_normalizer Y)
  rw [bar_lift] at this
  exact this.symm

theorem isPGroup_bar {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) : IsPGroup p (bar A X) :=
  (hX.comap_subtype (K := normalizer (A : Set G))).map _

theorem isPGroup_lift [Finite G] {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    {Y : Subgroup (Bar A)} (hY : IsPGroup p Y) : IsPGroup p (lift Y) := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hA
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hY
  refine IsPGroup.of_card (n := n + m) ?_
  rw [card_lift, hm, hn, pow_add]

end CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
