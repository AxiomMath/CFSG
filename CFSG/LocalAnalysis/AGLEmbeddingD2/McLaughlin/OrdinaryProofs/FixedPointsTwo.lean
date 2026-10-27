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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

theorem exists_ne_one_mem_centralizer_of_normalizes {G : Type} [Group G] [Finite G]
    {S U : Subgroup G} (hS : IsPGroup 2 S) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) :
    ∃ x ∈ U, x ≠ 1 ∧ ∀ s ∈ S, s * x = x * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S U :=
    { smul := fun s u => ⟨(s : G) * u * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSN s.2) (u : G)).mp u.2⟩
      one_smul := fun u => Subtype.ext
        (show ((1 : S) : G) * (u : G) * ((1 : S) : G)⁻¹ = u by simp)
      mul_smul := fun s t u => Subtype.ext
        (show ((s * t : S) : G) * (u : G) * ((s * t : S) : G)⁻¹ =
          (s : G) * ((t : G) * (u : G) * (t : G)⁻¹) * (s : G)⁻¹ by
          simp only [Subgroup.coe_mul, mul_inv_rev]; group) }
  let hact : MulAction S U := act
  have hnt : Nontrivial U := (U.nontrivial_iff_ne_bot).mpr hU1
  have hpU : 2 ∣ Nat.card U := by
    obtain ⟨n, hn0, hn⟩ := (hU.nontrivial_iff_card).mp hnt
    exact hn ▸ dvd_pow_self 2 (ne_of_gt hn0)
  have h1 : (1 : U) ∈ MulAction.fixedPoints S U := fun s =>
    Subtype.ext (by show (s : G) * 1 * (s : G)⁻¹ = 1; group)
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hpU h1
  refine ⟨(b : G), b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  have hsb : (⟨s, hs⟩ : S) • b = b := hb ⟨s, hs⟩
  have h2 : (s : G) * (b : G) * (s : G)⁻¹ = (b : G) := congrArg Subtype.val hsb
  exact (mul_inv_eq_iff_eq_mul.mp h2)

end CFSG.AGLEmbeddingD2.McLaughlin

end
