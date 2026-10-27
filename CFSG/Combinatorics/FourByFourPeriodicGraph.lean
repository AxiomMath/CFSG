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

namespace CFSG.Combinatorics.FourByFourPeriodicGraph

abbrev Vertex : Type :=
  (ZMod 4 × ZMod 4) × Fin 2

@[expose] def s : Fin 3 → ZMod 4 × ZMod 4 :=
  ![(0, 0), (1, 0), (0, 1)]

@[expose] def colourAdj (i : Fin 3) (p q : Vertex) : Prop :=
  (p.2 = 0 ∧ q.2 = 1 ∧ q.1 = p.1 + s i) ∨ (p.2 = 1 ∧ q.2 = 0 ∧ p.1 = q.1 + s i)

instance decidableColourAdj (i : Fin 3) : DecidableRel (colourAdj i) := fun p q =>
  inferInstanceAs (Decidable ((p.2 = 0 ∧ q.2 = 1 ∧ q.1 = p.1 + s i) ∨
    (p.2 = 1 ∧ q.2 = 0 ∧ p.1 = q.1 + s i)))

theorem colourAdj_symm {i : Fin 3} {p q : Vertex} (h : colourAdj i p q) : colourAdj i q p := by
  rcases h with ⟨hp, hq, h⟩ | ⟨hp, hq, h⟩
  · exact Or.inr ⟨hq, hp, h⟩
  · exact Or.inl ⟨hq, hp, h⟩

theorem side_ne_of_colourAdj {i : Fin 3} {p q : Vertex} (h : colourAdj i p q) : p.2 ≠ q.2 := by
  rcases h with ⟨hp, hq, -⟩ | ⟨hp, hq, -⟩ <;> rw [hp, hq] <;> decide

@[expose] def P4 : SimpleGraph Vertex where
  Adj p q := ∃ i, colourAdj i p q
  symm := ⟨fun _ _ ⟨i, h⟩ => ⟨i, colourAdj_symm h⟩⟩
  loopless := ⟨fun _ ⟨_, h⟩ => side_ne_of_colourAdj h rfl⟩

instance decidableAdj : DecidableRel P4.Adj := fun p q =>
  inferInstanceAs (Decidable (∃ i, colourAdj i p q))

theorem adj_iff_exists_colourAdj {p q : Vertex} : P4.Adj p q ↔ ∃ i, colourAdj i p q :=
  Iff.rfl

@[expose] def o : Vertex :=
  ((0, 0), 0)

@[expose] def IsColouredIso {W : Type*} (c : Fin 3 → W → W → Prop) (f : Vertex ≃ W) : Prop :=
  ∀ i p q, colourAdj i p q ↔ c i (f p) (f q)

@[expose] def nbr (p : Vertex) (i : Fin 3) : Vertex :=
  if p.2 = 0 then (p.1 + s i, 1) else (p.1 - s i, 0)

theorem s_injective : Function.Injective s := by
  decide

theorem colourAdj_iff_eq_nbr : ∀ (i : Fin 3) (p q : Vertex), colourAdj i p q ↔ q = nbr p i := by
  decide

theorem adj_iff {p q : Vertex} : P4.Adj p q ↔ ∃ i, q = nbr p i :=
  exists_congr fun i => colourAdj_iff_eq_nbr i p q

theorem colourAdj_unique : ∀ (i j : Fin 3) (p q : Vertex), colourAdj i p q → colourAdj j p q →
    i = j := by
  decide

theorem nbr_nbr : ∀ (p : Vertex) (i : Fin 3), nbr (nbr p i) i = p := by
  decide

theorem nbr_injective : ∀ (p : Vertex) (i j : Fin 3), nbr p i = nbr p j → i = j := by
  decide

theorem adj_nbr (p : Vertex) (i : Fin 3) : P4.Adj p (nbr p i) :=
  adj_iff.mpr ⟨i, rfl⟩

end CFSG.Combinatorics.FourByFourPeriodicGraph
