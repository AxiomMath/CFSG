module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtNbr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open scoped commutatorElement

section Exit

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hyp51At_of_tightInO2 (hΩ : HypOmegaGen Ω) {c t : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (htB : t ∈ B) (hc1 : c ≠ 1)
    (ht1 : t ≠ 1) (hct : t ≠ c) (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (h2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)))) : Hyp51At B c := by
  have hH : IsSubnormal (coreHull Ω c) ⊤ := by
    have := normal_coreHull hΩ hc2
    exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hq : Quiet c t htC := fun L hL => TL4.quiet_of_inO2_sub hH htH h2 L hL
  exact ⟨fun L₁ L₂ h₁ _ m₁ _ =>
      (moved_false_of_quiet hB htB hcB hc1 ht1 hct htC hq h₁ m₁).elim,
    fun L hL hm => (moved_false_of_quiet hB htB hcB hc1 ht1 hct htC hq hL hm).elim⟩

end Gen

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
