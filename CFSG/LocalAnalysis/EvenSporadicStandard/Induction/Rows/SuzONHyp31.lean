module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.LamLike2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.Sporadic.Schreier.ONOuterData
public import CFSG.Sporadic.SuzOddCore.CTIFirst

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.ONSchreier Cover

theorem commute_of_exp_two {X : Type*} [Group X] {P : Subgroup X} (h : ∀ x ∈ P, x * x = 1) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy => by
  have hxy : x * y * (x * y) = 1 := h _ (P.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

section Suz

@[expose] def SuzK2FixedNotLam2 : Prop :=
  ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
    Nonempty ((K₂ ⧸ center K₂) ≃* (↥suzD ⧸ center ↥suzD)) → InvolutionFixesNotLam2 K₂ 8

end Suz

end CFSG.EvenSporadicStandard.Induction
