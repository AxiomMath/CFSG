module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryGraph
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryLines
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryPair
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.D4RC (rcl_map_fix_eq)
open CFSG.RankThree.Classical2 (fixSubgroup)
open scoped Matrix MatrixGroups Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Aux

variable {G : Type*} [Group G]

theorem conj_twist_aux (τ : G →* G) (n a b : G) :
    n * τ (a * b * a⁻¹) * n⁻¹ =
      (n * τ a * n⁻¹) * (n * τ b * n⁻¹) * (n * τ a * n⁻¹)⁻¹ := by
  simp only [map_mul, map_inv]
  group

theorem conj_cancel_aux (g n a b : G) (h : g * n * a * (g * n)⁻¹ = g * b * g⁻¹) :
    n * a * n⁻¹ = b := by
  have h2 : g * (n * a * n⁻¹) * g⁻¹ = g * b * g⁻¹ := by
    rw [← h]
    group
  have h3 := mul_right_cancel h2
  exact mul_left_cancel h3

theorem sq_eq_one_aux (g a : G) (h : g * a * g⁻¹ * (g * a * g⁻¹) = 1) : a * a = 1 := by
  have h2 : g * (a * a) * g⁻¹ = 1 := by
    rw [← h]
    group
  have h3 : g * (a * a) = g := by
    have := congrArg (· * g) h2
    simpa [mul_assoc] using this
  exact mul_left_cancel (h3.trans (mul_one g).symm)

theorem invol_conj_aux (a x : G) (h : a * a = 1) : a * (a * x * a⁻¹) * a⁻¹ = x := by
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_right h
  rw [this]
  calc a * (a * x * a) * a = (a * a) * x * (a * a) := by simp only [mul_assoc]
    _ = x := by rw [h]; simp

theorem comm_of_conj_eq_aux (g a y : G) (h : a * y * a⁻¹ = y) :
    (g * a * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * a * g⁻¹) := by
  have h' : a * y = y * a := by
    have := congrArg (· * a) h
    simpa [mul_assoc] using this
  calc (g * a * g⁻¹) * (g * y * g⁻¹) = g * (a * y) * g⁻¹ := by group
    _ = g * (y * a) * g⁻¹ := by rw [h']
    _ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group

end Aux

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
