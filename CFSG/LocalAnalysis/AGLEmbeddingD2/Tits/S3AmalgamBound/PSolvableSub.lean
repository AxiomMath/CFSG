module

public import CFSG.GroupTheory.HallHigmanPiCore
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

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem isPSolvable_of_isSubnormal {p : ℕ} {X : Type*} [Group X]
    (hX : CFSG.HallHigman.IsPSolvable p X) {Y : Subgroup X} (hY : Y.IsSubnormal) :
    CFSG.HallHigman.IsPSolvable p ↥Y := by
  intro H hH T hT hs
  set H' : Subgroup X := H.map Y.subtype with hH'
  have hsub : H'.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (K := Y) ?_ ?_ hY
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · have : H'.subgroupOf Y = H :=
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective H
      rw [this]; exact hH
  let ψ : ↥H ≃* ↥H' := Subgroup.equivMapOfInjective H Y.subtype Y.subtype_injective
  have hψ : Function.Surjective ψ.toMonoidHom := ψ.surjective
  haveI hTn : (T.map ψ.toMonoidHom).Normal := Subgroup.Normal.map hT _ hψ
  have hiso : (↥H ⧸ T) ≃* (↥H' ⧸ T.map ψ.toMonoidHom) :=
    QuotientGroup.congr T (T.map ψ.toMonoidHom) ψ rfl
  have hs' : IsSimpleGroup (↥H' ⧸ T.map ψ.toMonoidHom) := by
    haveI := hs
    exact hiso.symm.isSimpleGroup
  have key := hX H' hsub (T.map ψ.toMonoidHom) hs'
  have hidx : (T.map ψ.toMonoidHom).index = T.index := by
    show Nat.card _ = Nat.card _
    exact (Nat.card_congr hiso.toEquiv).symm
  rw [hidx] at key
  exact key

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
