module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Basis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace Burnside

open CategoryTheory
open scoped BigOperators

namespace ClassFun

variable {G : Type} [Group G] [Fintype G]

private theorem IrrepCharBasis.repr_eq_card_inv_mul_pairing
    (B : ClassFun.IrrepCharBasis ℂ G) (f : ClassFun ℂ G) (i : B.ι) :
    B.b.repr f i =
      (Fintype.card G : ℂ)⁻¹ *
        _root_.CFSG.ClassFun.characterPairingLeft ℂ G f (ClassFun.character (B.V i)) := by
  classical
  let : ∀ j, Simple (B.V j) := B.simple
  let hcomplete := B.isCompleteSetOfSimples
  have hexpand :
      f = ∑ j : B.ι, (B.b.repr f j) • B.b j := by
    simp only [Module.Basis.sum_repr]
  have hpair :
      _root_.CFSG.ClassFun.characterPairingLeft ℂ G f (ClassFun.character (B.V i)) =
        (B.b.repr f i) * (Fintype.card G : ℂ) := by
    conv_lhs => rw [hexpand, map_sum]
    rw [LinearMap.sum_apply]
    simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [B.b_eq, _root_.CFSG.ClassFun.characterPairingLeft_character]
      simp
    · intro j _ hji
      rw [B.b_eq, _root_.CFSG.ClassFun.characterPairingLeft_character]
      have hno : ¬ Nonempty (B.V j ≅ B.V i) := by
        intro h
        exact hji (hcomplete.is_distinct j i h)
      simp [hno]
    · simp
  rw [hpair]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

private theorem pairing_conjClassIndicator_one
    (V : FDRep ℂ G) :
    _root_.CFSG.ClassFun.characterPairingLeft ℂ G
        (_root_.CFSG.ClassFun.conjClassIndicator ℂ (1 : G)) (ClassFun.character V) =
      (Module.finrank ℂ V : ℂ) := by
  classical
  rw [_root_.CFSG.ClassFun.characterPairingLeft_apply]
  simp only [_root_.CFSG.ClassFun.conjClassIndicator_apply, isConj_one_left]
  simp [FDRep.char_one]

theorem IrrepCharBasis.regular_character_relation
    (B : ClassFun.IrrepCharBasis ℂ G) {x : G} (hx : x ≠ 1) :
    ∑ i : B.ι,
        (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x = 0 := by
  classical
  let f : ClassFun ℂ G := _root_.CFSG.ClassFun.conjClassIndicator ℂ (1 : G)
  have hexpand :
      f = ∑ i : B.ι, (B.b.repr f i) • B.b i := by
    simp only [Module.Basis.sum_repr]
  have heval := congrArg (fun φ : ClassFun ℂ G => φ x) hexpand
  have hsum_inv :
      ∑ i : B.ι,
          (Fintype.card G : ℂ)⁻¹ *
            (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x = 0 := by
    simpa only [f, _root_.CFSG.ClassFun.conjClassIndicator_apply, isConj_one_left, hx, ite_false,
      _root_.CFSG.ClassFun.sum_apply, smul_eq_mul, Pi.smul_apply,
      _root_.CFSG.ClassFun.smul_apply, B.b_eq,
      ClassFun.char_apply,
      Burnside.ClassFun.IrrepCharBasis.repr_eq_card_inv_mul_pairing,
      pairing_conjClassIndicator_one] using heval.symm
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    ∑ i : B.ι,
        (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x =
        (Fintype.card G : ℂ) *
          ∑ i : B.ι,
            (Fintype.card G : ℂ)⁻¹ *
              (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ = 0 := by rw [hsum_inv, mul_zero]

end ClassFun

end Burnside

end CFSG
