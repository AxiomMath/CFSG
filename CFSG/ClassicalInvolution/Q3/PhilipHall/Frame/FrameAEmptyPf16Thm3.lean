module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf13Rows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf12L3E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Rows

variable {Y : Type} [Group Y]

structure TypeRHyp (Ω : Set (Subgroup Y)) : Prop where
  hyp : HypOmegaGen Ω
  twoGroup : ∀ J ∈ Ω, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  sylow : ∀ J ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)

@[expose] def Thm3RowG2 (P : Subgroup Y) : Prop :=
  ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Blueprint.LieModel (SecQuot P) .G2 0 p f

@[expose] def Thm3RowU3 (P : Subgroup Y) : Prop :=
  ∃ (N : Subgroup (SecQuot P)) (_ : N.Normal), N.index = 2 ∧
    CFSG.Blueprint.LieModel ↥N .PSU 3 3 1

@[expose] def Thm3RowM12 (P : Subgroup Y) : Prop :=
  CFSG.Blueprint.NativeSporadic.IsSporadic (SecQuot P) .M12

@[expose] def Thm3RowL3E8 (P : Subgroup Y) : Prop := IsL3E8 (SecQuot P)

@[expose] def Thm3RowW (Ω : Set (Subgroup Y)) (P : Subgroup Y) : Prop :=
  ∃ (W : Subgroup (SecQuot P)) (_ : W.Normal),
    WSet (oddQuotientFamily (restrictFamily Ω P)) = {W} ∧
      Nonempty ((SecQuot P ⧸ W) ≃* DihedralGroup 6)

end Rows

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
