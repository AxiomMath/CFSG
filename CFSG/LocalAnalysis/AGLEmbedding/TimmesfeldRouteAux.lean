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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.AGLEmbedding

open Subgroup

theorem center_quotient_center_eq_bot_of_commutator_eq_top {D : Type*} [Group D]
    (hD : commutator (D ⧸ center D) = ⊤) : center (D ⧸ center D) = ⊥ := by
  let mk := QuotientGroup.mk' (center D)
  let Z₂ := (center (D ⧸ center D)).comap mk
  have hZ₂ : ⁅Z₂, (⊤ : Subgroup D)⁆ ≤ center D := by
    rw [Subgroup.commutator_le]
    intro z hz d _
    rw [← QuotientGroup.ker_mk' (center D), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz (mk d)).symm
  have hc : ⁅center D, (⊤ : Subgroup D)⁆ = ⊥ :=
    commutator_top_right_eq_bot_iff_le_center.mpr le_rfl
  have h3 : ⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, Z₂⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (⊤ : Subgroup D) Z₂]
      exact le_bot_iff.mp ((commutator_mono hZ₂ le_rfl).trans hc.le)
    · exact le_bot_iff.mp ((commutator_mono hZ₂ le_rfl).trans hc.le)
  have hsup : commutator D ⊔ center D = ⊤ := by
    have hmap : (commutator D).map mk = ⊤ := by
      rw [commutator_def, map_commutator, map_top_of_surjective mk
        (QuotientGroup.mk'_surjective _), ← commutator_def, hD]
    have h := congrArg (Subgroup.comap mk) hmap
    rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at h
  have hcent : ⊤ ≤ centralizer (Z₂ : Set D) := by
    rw [← hsup]
    refine sup_le ?_ (center_le_centralizer _)
    rw [commutator_def]
    exact (commutator_eq_bot_iff_le_centralizer).mp h3
  have hle : Z₂ ≤ center D := by
    rw [← commutator_top_right_eq_bot_iff_le_center, commutator_comm,
      commutator_eq_bot_iff_le_centralizer]
    exact hcent
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (center D) x
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff d).mpr (hle hx)

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : center Y = ⊥) : center X = ⊥ := by
  rw [← map_center_eq e] at hY
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hY

theorem center_eq_bot_of_mulEquiv_quotient_center {X D : Type*} [Group X] [Group D]
    (e : X ≃* D ⧸ center D) (hX : commutator X = ⊤) : center X = ⊥ := by
  have : Group.IsPerfect X := ⟨hX⟩
  have hQ : Group.IsPerfect (D ⧸ center D) :=
    Group.IsPerfect.ofSurjective (f := (e : X →* D ⧸ center D)) e.surjective
  exact center_eq_bot_of_mulEquiv e
    (center_quotient_center_eq_bot_of_commutator_eq_top hQ.commutator_eq_top)

theorem center_specialLinearGroup_fin_two_eq_bot {F : Type*} [Field F] [CharP F 2] :
    center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hsq : (r - 1) ^ 2 = 0 := by
    calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
      _ = 0 := by rw [hr, CharTwo.two_eq_zero, zero_mul, sub_zero, one_add_one_eq_two,
        CharTwo.two_eq_zero]
  have hr1 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

end CFSG.AGLEmbedding
