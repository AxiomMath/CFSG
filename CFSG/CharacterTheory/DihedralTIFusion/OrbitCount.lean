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

namespace CFSG.DihedralTIFusion

theorem natCard_range_eq_index {N α : Type*} [Group N] (K : Subgroup N) (f : N → α)
    (hf : ∀ n m : N, f n = f m ↔ n⁻¹ * m ∈ K) : Nat.card (Set.range f) = K.index := by
  let g : N ⧸ K → α := Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((hf _ _).mp hab)
  have hrange : Set.range f = Set.range g := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H n => exact ⟨n, rfl⟩
  rw [hrange, Nat.card_range_of_injective hg]
  rfl

theorem natCard_orbits_mul {α : Type*} {S : Set α} [Finite S] (orb : α → Set α) (e : ℕ)
    (hsub : ∀ s ∈ S, orb s ⊆ S) (hself : ∀ s ∈ S, s ∈ orb s)
    (hsame : ∀ s ∈ S, ∀ t ∈ orb s, orb t = orb s) (hcard : ∀ s ∈ S, Nat.card (orb s) = e) :
    Nat.card {O : Set α | ∃ s ∈ S, O = orb s} * e = Nat.card S := by
  set B := {O : Set α | ∃ s ∈ S, O = orb s}
  let π : S → B := fun s => ⟨orb s, s, s.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨O, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  have : Finite B := Finite.of_surjective π hπ
  have : Fintype B := Fintype.ofFinite _
  have hfiber : ∀ O : B, Nat.card {s : S // π s = O} = e := by
    rintro ⟨O, s₀, hs₀, rfl⟩
    rw [← hcard s₀ hs₀]
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, ?_⟩
        invFun := fun t => ⟨⟨t.1, hsub s₀ hs₀ t.2⟩, Subtype.ext (hsame s₀ hs₀ t.1 t.2)⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
    have h : orb s.1.1 = orb s₀ := congrArg Subtype.val s.2
    have hmem : s.1.1 ∈ orb s.1.1 := hself _ s.1.2
    rwa [h] at hmem
  calc Nat.card B * e = ∑ _O : B, e := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    _ = ∑ O : B, Nat.card {s : S // π s = O} := Finset.sum_congr rfl fun O _ => (hfiber O).symm
    _ = Nat.card (Σ O : B, {s : S // π s = O}) := Nat.card_sigma.symm
    _ = Nat.card S := Nat.card_congr (Equiv.sigmaFiberEquiv π)

end CFSG.DihedralTIFusion
