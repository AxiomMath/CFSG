module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Basis
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace Burnside

open CategoryTheory
open scoped BigOperators

namespace ClassFun

variable {G : Type} [Group G] [Fintype G]

theorem IrrepCharBasis.rho_ne_one_of_ne_of_character_eq_one
    (B : ClassFun.IrrepCharBasis ℂ G) {i i₀ : B.ι}
    (hi : i ≠ i₀) (hi₀char : ClassFun.character (B.V i₀) = 1) :
    (B.V i).ρ ≠ 1 := by
  classical
  let : Simple (B.V i) := B.simple i
  let : Simple (B.V i₀) := B.simple i₀
  intro hρ
  have hnoniso : IsEmpty (B.V i₀ ≅ B.V i) :=
    (_root_.CFSG.ClassFun.IrrepCharBasis.isCompleteSetOfSimples B).isEmpty_iso_of_ne hi.symm
  have hhomzero : Module.finrank ℂ ((B.V i₀) ⟶ (B.V i)) = 0 :=
    FDRep.finrank_hom_eq_zero_of_not_iso_simple hnoniso
  have horth := FDRep.char_scalarProduct_eq_finrank_hom
    (k := ℂ) (G := G) (B.V i) (B.V i₀)
  rw [hhomzero, Nat.cast_zero] at horth
  have hchari : ∀ g : G,
      (B.V i).character g = (Module.finrank ℂ (B.V i) : ℂ) := by
    intro g
    change LinearMap.trace ℂ (B.V i) ((B.V i).ρ g) = _
    rw [hρ]
    simp
  have hi₀eval : ∀ g : G, (B.V i₀).character g = 1 := by
    intro g
    have h := DFunLike.congr_fun hi₀char g
    simpa using h
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hdimzero : (Module.finrank ℂ (B.V i) : ℂ) = 0 := by
    have horth' :
        (Fintype.card G : ℂ)⁻¹ *
          ((Fintype.card G : ℂ) * (Module.finrank ℂ (B.V i) : ℂ)) = 0 := by
      simpa only [hchari, hi₀eval, mul_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] using horth
    field_simp at horth'
    exact horth'
  let : Nontrivial (B.V i) := FDRep.nontrivial_of_simple (B.V i)
  have hdimpos : 0 < Module.finrank ℂ (B.V i) := Module.finrank_pos
  have hdimne : (Module.finrank ℂ (B.V i) : ℂ) ≠ 0 := by
    exact_mod_cast hdimpos.ne'
  exact hdimne hdimzero

end ClassFun

end Burnside

end CFSG
