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

namespace CFSG.GH74.KGroups

@[expose] def permHomOf (H : Type*) [Group H] {X : Type*} [MulAction H X] {N : ℕ}
    (E : Fin N ≃ X) : H →* Equiv.Perm (Fin N) where
  toFun g := E.trans ((MulAction.toPerm g).trans E.symm)
  map_one' := by
    ext i
    simp
  map_mul' g h := by
    ext i
    simp [mul_smul]

section

variable {H X : Type*} [Group H] [MulAction H X] {N : ℕ}

theorem permHomOf_apply (E : Fin N ≃ X) (g : H) (i : Fin N) :
    E (permHomOf H E g i) = g • E i := by
  simp [permHomOf]

theorem permHomOf_injective [FaithfulSMul H X] (E : Fin N ≃ X) :
    Function.Injective (permHomOf H E) := by
  intro g h hgh
  have : (MulAction.toPerm g : Equiv.Perm X) = MulAction.toPerm h := by
    ext x
    have := congrArg (fun σ : Equiv.Perm (Fin N) => E (σ (E.symm x))) hgh
    simpa [permHomOf_apply] using this
  exact MulAction.toPerm_injective this

theorem permHomOf_eq (E : Fin N ≃ X) (g : H) (p : Equiv.Perm (Fin N))
    (h : ∀ i, E (p i) = g • E i) : permHomOf H E g = p := by
  refine Equiv.ext fun i => E.injective ?_
  rw [permHomOf_apply, h]

end

theorem equiv_closure_of_hom {H : Type*} [Group H] [Finite H] {N : ℕ}
    (f : H →* Equiv.Perm (Fin N)) (hf : Function.Injective f) (a b : H)
    (pa pb : Equiv.Perm (Fin N)) (ha : f a = pa) (hb : f b = pb)
    (P : Subgroup (Equiv.Perm (Fin N))) (hP : P = Subgroup.closure {pa, pb})
    (hcard : Nat.card P = Nat.card H) : Nonempty (H ≃* P) := by
  have hrange : P = f.range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hP, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨a, ha⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨b, hb⟩
    · rw [hcard, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange.symm)⟩

end CFSG.GH74.KGroups
