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

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

@[expose] def NormMax {X : Type*} [Group X] (R : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, Subgroup.normalizer (R : Set X) ≤ Y →
    Y = Subgroup.normalizer (R : Set X) ∨ Y = ⊤

variable {X Y : Type*} [Group X] [Group Y]

theorem NormMax.map {R : Subgroup X} (e : X ≃* Y) (h : NormMax R) :
    NormMax (R.map e.toMonoidHom) := by
  intro Y' hY'
  have hnorm : Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (R : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R e).symm
  rw [hnorm] at hY' ⊢
  have h1 : Subgroup.normalizer (R : Set X) ≤ Y'.comap e.toMonoidHom := by
    intro x hx
    exact hY' ⟨x, hx, rfl⟩
  rcases h _ h1 with h2 | h2
  · left
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y', h2]
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y', h2,
      Subgroup.map_top_of_surjective _ e.surjective]

theorem NormMax.sylow {p : ℕ} [Fact p.Prime] [Finite X] (R₀ R : Sylow p X)
    (h : NormMax (R₀ : Subgroup X)) : NormMax (R : Subgroup X) := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R₀ R
  have hRc : (R : Subgroup X) = (R₀ : Subgroup X).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  rw [hRc]
  exact h.map (MulAut.conj c)

theorem NormMax.sylow_of_equiv {p : ℕ} [Fact p.Prime] [Finite X] [Finite Y] (e : X ≃* Y)
    (R₀ : Sylow p Y) (h : NormMax (R₀ : Subgroup Y)) (R : Sylow p X) :
    NormMax (R : Subgroup X) := by
  have h1 := h.map e.symm
  have hcard : Nat.card ((R₀ : Subgroup Y).map e.symm.toMonoidHom) =
      p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, Sylow.card_eq_multiplicity R₀,
      Nat.card_congr e.toEquiv]
  exact NormMax.sylow (Sylow.ofCard _ hcard) R h1

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
