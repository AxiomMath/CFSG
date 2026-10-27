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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G K A : Type*} [Group G] [Group K] [Group A]
variable [MulDistribMulAction A G] [MulDistribMulAction A K]

@[instance_reducible]
def equivariantFiberAction (hom : G →* K)
    (hequivariant : ∀ actor : A, ∀ element : G, hom (actor • element) = actor • hom element)
    (value : K) (hfixed : ∀ actor : A, actor • value = value) :
    MulAction A {element : G // hom element = value} where
  smul actor element := ⟨actor • element.val, by
    rw [hequivariant, element.property, hfixed]⟩
  one_smul element := Subtype.ext (one_smul A element.val)
  mul_smul first second element := Subtype.ext (mul_smul first second element.val)

theorem coprime_pgroup_fixed_lift [Finite G] (prime : ℕ) [Fact (Nat.Prime prime)]
    (hpgroup : IsPGroup prime A) (hom : G →* K)
    (hequivariant : ∀ actor : A, ∀ element : G, hom (actor • element) = actor • hom element)
    (hcoprime : ¬ prime ∣ Nat.card hom.ker)
    (value : K) (hrange : value ∈ hom.range) (hfixed : ∀ actor : A, actor • value = value) :
    ∃ element : G, hom element = value ∧ ∀ actor : A, actor • element = element := by
  obtain ⟨base, hbase⟩ := hrange
  let _ := equivariantFiberAction hom hequivariant value hfixed
  have hcard : Nat.card {element : G // hom element = value} = Nat.card hom.ker := by
    rw [← hbase]
    exact Nat.card_congr (hom.fiberEquivKer base)
  obtain ⟨element, helement⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    {element : G // hom element = value} (hcard ▸ hcoprime)
  refine ⟨element.val, element.property, ?_⟩
  intro actor
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp helement actor)

end CFSG.DisconnectedInvolutionGraph.Helpers
