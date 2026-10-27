module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GluePSULie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
  CFSG.ClassicalInvolution.Disconnected.AschTight

section TwinIdentFinal

theorem model1520LieTarget_psu : Model1520LieTarget .PSU 4 :=
  fun _ _ _ X _ _ D i hi hk _ hL _ hLt =>
    model1520_of_lieSystem3_all X D i hi .PSU 4 (Or.inr ⟨rfl, rfl⟩) hk hL hLt

theorem twinIdent_model1520_of_triality {G : Type} [Group G] [Finite G] (X : Subgroup G) {n : ℕ}
    (hTri : Model1520LieTarget .POmegaPlus 4)
    (hBelow : CIT3Below n) (hlt : Nat.card ↥X < n) (hO : classicalInvolutionOddCore ↥X = ⊥)
    {J : Subgroup ↥X} {z : ↥X} (hΩ : HypOmegaGen (CoreAssembly.conjClass J)) (h2 : IsPGroup 2 J)
    (hgen : (⨆ K ∈ CoreAssembly.conjClass J, K) = ⊤)
    (hl : HasLifts (CoreAssembly.conjClass J)) (hz : IsUniqueInvolution J z) {J' : Subgroup ↥X}
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass J) J) (hne : J' ≠ J) :
    Model1520 X (z : G) :=
  twinIdent_model1520 X model1520LieTarget_psu hTri hBelow hlt hO hΩ h2 hgen hl hz hJ' hne

end TwinIdentFinal

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
