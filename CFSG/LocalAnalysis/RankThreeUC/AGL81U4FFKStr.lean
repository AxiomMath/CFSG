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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.RankThreeUC

theorem natCard_adjoinRoot {m : Polynomial (ZMod 2)} (hm : Irreducible m) :
    haveI : Fact (Irreducible m) := ⟨hm⟩
    Finite (AdjoinRoot m) ∧ CharP (AdjoinRoot m) 2 ∧ Nat.card (AdjoinRoot m) = 2 ^ m.natDegree := by
  haveI : Fact (Irreducible m) := ⟨hm⟩
  haveI hfin : Module.Finite (ZMod 2) (AdjoinRoot m) :=
    (AdjoinRoot.powerBasis hm.ne_zero).finite
  have hrank : Module.finrank (ZMod 2) (AdjoinRoot m) = m.natDegree := by
    rw [PowerBasis.finrank]
    exact AdjoinRoot.powerBasis_dim hm.ne_zero
  refine ⟨Module.finite_of_finite (ZMod 2), ?_, ?_⟩
  · exact charP_of_injective_algebraMap
      (RingHom.injective (algebraMap (ZMod 2) (AdjoinRoot m))) 2
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hrank]

theorem exists_adjoinRoot_module {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (φ : Module.End (ZMod 2) E) (m : Polynomial (ZMod 2)) (hm : Irreducible m)
    (hφ : Polynomial.aeval φ m = 0) :
    haveI : Fact (Irreducible m) := ⟨hm⟩
    ∃ _ : Module (AdjoinRoot m) E,
      (∀ (c : ZMod 2) (x : E), (algebraMap (ZMod 2) (AdjoinRoot m) c) • x = c • x) ∧
      (∀ x : E, AdjoinRoot.root m • x = φ x) ∧
      (∀ ψ : Module.End (ZMod 2) E, ψ * φ = φ * ψ →
        ∀ (c : AdjoinRoot m) (x : E), ψ (c • x) = c • ψ x) := by
  have hker : ∀ a : Polynomial (ZMod 2), a ∈ Ideal.span {m} → Polynomial.aeval φ a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, hφ, zero_mul]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : AdjoinRoot m →+* Module.End (ZMod 2) E,
      ∀ p : Polynomial (ZMod 2), Φ (AdjoinRoot.mk m p) = Polynomial.aeval φ p :=
    ⟨Ideal.Quotient.lift (Ideal.span {m}) (Polynomial.aeval φ).toRingHom hker, fun p => rfl⟩
  have hΦroot : Φ (AdjoinRoot.root m) = φ := by
    show Φ (AdjoinRoot.mk m Polynomial.X) = φ
    rw [hΦ, Polynomial.aeval_X]
  have hΦalg : ∀ c : ZMod 2,
      Φ (algebraMap (ZMod 2) (AdjoinRoot m) c) = algebraMap (ZMod 2) (Module.End (ZMod 2) E) c := by
    intro c
    have h : algebraMap (ZMod 2) (AdjoinRoot m) c = AdjoinRoot.mk m (Polynomial.C c) := rfl
    rw [h, hΦ, Polynomial.aeval_C]
  refine ⟨Module.compHom E Φ, ?_, ?_, ?_⟩
  · intro c x
    show Φ (algebraMap (ZMod 2) (AdjoinRoot m) c) x = c • x
    rw [hΦalg c, Module.algebraMap_end_apply]
  · intro x
    show Φ (AdjoinRoot.root m) x = φ x
    rw [hΦroot]
  · intro ψ hψ c x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
    have hcomm : Commute ψ (Polynomial.aeval φ p) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute
        (Polynomial.aeval_mem_adjoin_singleton _ _) hψ
    show ψ (Φ (AdjoinRoot.mk m p) x) = Φ (AdjoinRoot.mk m p) (ψ x)
    rw [hΦ]
    exact congrArg (fun g : Module.End (ZMod 2) E => g x) hcomm.eq

end CFSG.LocalAnalysis.RankThreeUC
