module

public import CFSG.GroupTheory.PCore.Defs
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

namespace CFSG

namespace BrauerSuzuki

universe u

theorem normal_le_oddCore_of_coprime_two
    {G : Type u} [Group G] (N : Subgroup G)
    (hN : N.Normal) (hcop : Nat.Coprime 2 (Nat.card N)) :
    N ≤ oddCore G := by
  exact le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩

theorem quotient_center_mono
    {G : Type u} [Group G] {N O : Subgroup G}
    [N.Normal] [O.Normal] (hNO : N ≤ O) {t : G}
    (ht : QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N)) :
    QuotientGroup.mk' O t ∈ Subgroup.center (G ⧸ O) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O x
  let f : G ⧸ N →* G ⧸ O :=
    QuotientGroup.map N O (MonoidHom.id G) (by simpa using hNO)
  have hcomm := Subgroup.mem_center_iff.mp ht (QuotientGroup.mk' N g)
  have hmapped := congrArg f hcomm
  simpa [f] using hmapped

theorem center_mod_oddCore_of_center_mod_coprime_two
    {G : Type u} [Group G] (N : Subgroup G)
    (hN : N.Normal) (hcop : Nat.Coprime 2 (Nat.card N)) {t : G}
    (ht : QuotientGroup.mk' N t ∈ Subgroup.center (G ⧸ N)) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) := by
  let : N.Normal := hN
  exact quotient_center_mono (normal_le_oddCore_of_coprime_two N hN hcop) ht

end BrauerSuzuki

end CFSG
