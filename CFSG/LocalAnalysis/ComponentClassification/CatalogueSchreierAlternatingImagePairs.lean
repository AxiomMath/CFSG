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
public import Mathlib.Tactic.Basify
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

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating

@[expose] noncomputable def ImagePairOrders {G : Type*} [Group G] (x y : G) :
    Set (G × G) :=
  {pair | orderOf pair.1 = orderOf x ∧ orderOf pair.2 = orderOf y ∧
    orderOf (pair.1 * pair.2) = orderOf (x * y) ∧
    orderOf (pair.1 * pair.2 * pair.1⁻¹ * pair.2⁻¹) = orderOf (x * y * x⁻¹ * y⁻¹)}

@[expose] noncomputable def imagePairEvaluation {G : Type*} [Group G] (x y : G) :
    MulAut G → ImagePairOrders x y := fun automorphism =>
  ⟨(automorphism x, automorphism y), by
    simp only [ImagePairOrders, Set.mem_ofPred_eq, MulEquiv.orderOf_eq,
      ← map_mul, ← map_inv, and_self]⟩

theorem imagePairEvaluation_injective {G : Type*} [Group G] (x y : G)
    (hgeneration : Subgroup.closure ({x, y} : Set G) = ⊤) :
    Function.Injective (imagePairEvaluation x y) := by
  intro first second hevaluation
  have hpairs := congrArg Subtype.val hevaluation
  have hx : first x = second x := congrArg Prod.fst hpairs
  have hy : first y = second y := congrArg Prod.snd hpairs
  have hgenerators : Set.EqOn (first : G → G) second ({x, y} : Set G) := by
    intro element helement
    rcases Set.mem_insert_iff.mp helement with rfl | helement
    · exact hx
    · exact Set.mem_singleton_iff.mp helement ▸ hy
  have hclosure := MonoidHom.eqOn_closure
    (f := first.toMonoidHom) (g := second.toMonoidHom) hgenerators
  rw [hgeneration] at hclosure
  exact MulEquiv.ext (fun element => hclosure (by simp))

theorem automorphism_card_le_image_pairs {G : Type*} [Group G] [Finite G] (x y : G)
    (hgeneration : Subgroup.closure ({x, y} : Set G) = ⊤) :
    Nat.card (MulAut G) ≤ Nat.card (ImagePairOrders x y) :=
  Nat.card_le_card_of_injective (imagePairEvaluation x y)
    (imagePairEvaluation_injective x y hgeneration)

end CFSG.ComponentClassification.CatalogueSchreierAlternating
