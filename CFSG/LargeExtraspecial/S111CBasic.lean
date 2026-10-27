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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LargeExtraspecial.S11

open Subgroup

variable {H : Type*} [Group H]

theorem mem_normalizer_inf {U V : Subgroup H} {x : H} (hU : x ∈ normalizer (U : Set H))
    (hV : x ∈ normalizer (V : Set H)) : x ∈ normalizer ((U ⊓ V : Subgroup H) : Set H) := by
  rw [mem_normalizer_iff] at hU hV ⊢
  intro w
  rw [mem_inf, mem_inf, hU w, hV w]

theorem mem_normalizer_sSup {s : Set (Subgroup H)} {x : H}
    (hx : ∀ L ∈ s, x ∈ normalizer (L : Set H)) :
    x ∈ normalizer ((sSup s : Subgroup H) : Set H) := by
  rw [mem_normalizer_iff_map_conj_eq, (gc_map_comap _).l_sSup, sSup_eq_iSup]
  exact iSup_congr fun L => iSup_congr fun hL => mem_normalizer_iff_map_conj_eq.mp (hx L hL)

theorem isPGroup_sSup_of_le_normalizer [Finite H] {p : ℕ} {𝒦 : Set (Subgroup H)}
    (hp : ∀ K ∈ 𝒦, IsPGroup p K) (hn : ∀ K ∈ 𝒦, ∀ L ∈ 𝒦, K ≤ normalizer (L : Set H)) :
    IsPGroup p (sSup 𝒦 : Subgroup H) := by
  refine Set.Finite.induction_on_subset (motive := fun s _ => IsPGroup p (sSup s : Subgroup H))
    𝒦 (Set.toFinite 𝒦) ?_ ?_
  · rw [sSup_empty]
    exact IsPGroup.of_bot
  · intro K t hK hts _ ih
    rw [sSup_insert]
    exact (hp K hK).to_sup_of_normal_right' ih fun x hx =>
      mem_normalizer_sSup fun L hL => hn K hK L (hts hL) hx

theorem le_normalizer_of_weaklyClosed {p : ℕ} [Fact p.Prime] {P L : Subgroup H} [Finite P]
    (hP : IsPGroup p P) (hLP : L ≤ P)
    (hwc : ∀ x ∈ P, L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set H) →
      L.map (MulAut.conj x).toMonoidHom = L) :
    P ≤ normalizer (L : Set H) := by
  have := hP.isNilpotent
  set N : Subgroup P := (normalizer (L : Set H)).subgroupOf P
  suffices hN : N = ⊤ by
    intro x hx
    have h : (⟨x, hx⟩ : P) ∈ N := hN ▸ mem_top _
    exact mem_subgroupOf.mp h
  by_contra hne
  have hlt := Group.normalizerCondition_of_isNilpotent N (lt_top_iff_ne_top.mpr hne)
  obtain ⟨x, hxN, hxn⟩ := IsConcreteLE.exists_of_lt hlt
  apply hxn
  rw [mem_subgroupOf, mem_normalizer_iff_map_conj_eq]
  apply hwc x x.2
  rintro _ ⟨y, hy, rfl⟩
  have hyN : (⟨y, hLP hy⟩ : P) ∈ N := mem_subgroupOf.mpr (le_normalizer hy)
  exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hxN _).mp hyN)

theorem exists_ne_one_commute_of_le_normalizer {p : ℕ} [Fact p.Prime] {P X : Subgroup H}
    [Finite P] (hP : IsPGroup p P) (hXP : X ≤ P) (hX : X ≠ ⊥)
    (hn : P ≤ normalizer (X : Set H)) : ∃ t ∈ X, t ≠ 1 ∧ ∀ x ∈ P, x * t = t * x := by
  have := hP.isNilpotent
  have : (X.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hXP).mpr hn
  have hX' : X.subgroupOf P ≠ ⊥ := by
    intro h
    apply hX
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hXP hy⟩ : P) ∈ X.subgroupOf P := mem_subgroupOf.mpr hy
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hX')
  refine ⟨t, mem_subgroupOf.mp (mem_inf.mp ht).1, fun h => ht1 (Subtype.ext (Subtype.ext h)),
    fun x hx => ?_⟩
  have hc := mem_center_iff.mp (mem_inf.mp ht).2 ⟨x, hx⟩
  exact congrArg Subtype.val hc

theorem le_map_sylow_of_le_normalizer {p : ℕ} {B : Subgroup H} (P : Sylow p B) {Y : Subgroup H}
    (hYB : Y ≤ B) (hY : IsPGroup p Y)
    (hn : (P : Subgroup B).map B.subtype ≤ normalizer (Y : Set H)) :
    Y ≤ (P : Subgroup B).map B.subtype := by
  have hY' : IsPGroup p (Y.subgroupOf B) := hY.comap_of_injective B.subtype Subtype.val_injective
  have hPn : (P : Subgroup B) ≤ normalizer ((Y.subgroupOf B : Subgroup B) : Set B) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro w
    rw [mem_subgroupOf, mem_subgroupOf]
    exact (mem_normalizer_iff.mp (hn ⟨x, hx, rfl⟩)) w
  have hmax := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' hY' hPn) le_sup_left
  intro y hy
  have h1 : (⟨y, hYB hy⟩ : B) ∈ (P : Subgroup B) :=
    hmax ▸ (le_sup_right : Y.subgroupOf B ≤ _) (mem_subgroupOf.mpr hy)
  exact ⟨_, h1, rfl⟩

end CFSG.LargeExtraspecial.S11
