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
public import Mathlib.RepresentationTheory.Character
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

namespace CFSG

@[expose] def BlocksIrr (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ}

@[expose] def BlocksVChar (G : Type*) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure (BlocksIrr G)

@[expose] def BlocksIsClassFunction {G : Type*} [Group G] (f : G → ℂ) : Prop :=
  ∀ g h : G, f (h * g * h⁻¹) = f g

@[expose] def BlocksBrauerElementary (E : Type*) [Group E] : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ C P : Subgroup E, IsCyclic C ∧ ¬ p ∣ Nat.card C ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ u ∈ P, c * u = u * c) ∧ ∀ e : E, ∃ c ∈ C, ∃ u ∈ P, e = c * u

@[expose] def BlocksIsPPart (p : ℕ) {G : Type*} [Group G] (g a : G) : Prop :=
  ∃ b : G, a * b = g ∧ b * a = g ∧ (∃ n : ℕ, orderOf a = p ^ n) ∧ 0 < orderOf b ∧
    Nat.Coprime (orderOf b) p

abbrev BlocksAlgInt : Subalgebra ℤ ℂ := integralClosure ℤ ℂ

@[expose] def BlocksLocalRing (m : Ideal BlocksAlgInt) : Set ℂ :=
  {z | ∃ a b : BlocksAlgInt, b ∉ m ∧ z = (a : ℂ) / (b : ℂ)}

@[expose] def BlocksLocalMaxIdeal (m : Ideal BlocksAlgInt) : Set ℂ :=
  {z | ∃ a b : BlocksAlgInt, a ∈ m ∧ b ∉ m ∧ z = (a : ℂ) / (b : ℂ)}

@[expose] noncomputable def BlocksIdempotentCoeff (G : Type*) [Group G] (A : Set (G → ℂ)) (g : G) : ℂ :=
  ∑ᶠ χ ∈ A, χ 1 / (Nat.card G : ℂ) * χ g⁻¹

@[expose] def BlocksAdmissible (m : Ideal BlocksAlgInt) (G : Type*) [Group G] (A : Set (G → ℂ)) : Prop :=
  A ⊆ BlocksIrr G ∧ ∀ g : G, BlocksIdempotentCoeff G A g ∈ BlocksLocalRing m

@[expose] def BlocksBlockOf (m : Ideal BlocksAlgInt) (G : Type*) [Group G] (χ : G → ℂ) : Set (G → ℂ) :=
  {ψ | ψ ∈ BlocksIrr G ∧ ∀ A : Set (G → ℂ), BlocksAdmissible m G A → (χ ∈ A ↔ ψ ∈ A)}

@[expose] def BlocksIsBlock (m : Ideal BlocksAlgInt) (G : Type*) [Group G] (B : Set (G → ℂ)) : Prop :=
  ∃ χ ∈ BlocksIrr G, B = BlocksBlockOf m G χ

@[expose] def BlocksPrincipalBlock (m : Ideal BlocksAlgInt) (G : Type*) [Group G] : Set (G → ℂ) :=
  BlocksBlockOf m G (fun _ => 1)

@[expose] def BlocksIsCentralR (m : Ideal BlocksAlgInt) {G : Type*} [Group G] (z : G → ℂ) : Prop :=
  (∀ g : G, z g ∈ BlocksLocalRing m) ∧ ∀ g h : G, z (h * g * h⁻¹) = z g

@[expose] noncomputable def BlocksCentralChar {G : Type*} [Group G] (χ z : G → ℂ) : ℂ :=
  (∑ᶠ g : G, z g * χ g) / χ 1

@[expose] noncomputable def BlocksBrauerProj {G : Type*} [Group G] (P H : Subgroup G) (z : G → ℂ) :
    H → ℂ :=
  Set.indicator {h : H | (h : G) ∈ Subgroup.centralizer (P : Set G)} (fun h => z h)

@[expose] def BlocksBrauerCorr (m : Ideal BlocksAlgInt) {G : Type*} [Group G] (P H : Subgroup G)
    (β : Set (H → ℂ)) (B : Set (G → ℂ)) : Prop :=
  ∀ z : G → ℂ, BlocksIsCentralR m z → ∀ χ ∈ B, ∀ ψ ∈ β,
    BlocksCentralChar χ z - BlocksCentralChar ψ (BlocksBrauerProj P H z) ∈ BlocksLocalMaxIdeal m

end CFSG
