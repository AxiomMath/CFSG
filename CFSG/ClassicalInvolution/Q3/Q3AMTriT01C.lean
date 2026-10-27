module

public import CFSG.ClassicalInvolution.Q3.Q3AMTriT01B
public import CFSG.ClassicalInvolution.Q3.Q3AMTri
public import CFSG.ClassicalInvolution.Q3.Q3AMTriT00
public import CFSG.ClassicalInvolution.Q3.Q3AMLYShape

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Main


theorem pspTableLeaf_proved : PspTableLeaf := by
  intro _ G _ _ _ Ω K J S R T W z t K' _ h
  obtain ⟨hz, J₁, J₂, hJ₁, hJ₂, hne, hcomm, a, b, ha, hb, hab, hzb, hcen⟩ := h.exists_layerPair
  have hbad := h.bad
  have hstd := hbad.std
  obtain ⟨ι, hfin, ⟨D⟩⟩ := nbrLayer_lieSystem hbad h.intrinsic hstd.stand.mem hstd.hz
  have hcl3 := layerFam_inClass3 hbad h.intrinsic hstd.stand.mem hstd.hz
  have hO : classicalInvolutionOddCore (↥(nbrLayer Ω K z) ⧸
      classicalInvolutionOddCore ↥(nbrLayer Ω K z)) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree _
  have hnc : ∀ L ∈ layerFam Ω K z, ¬ Commutes L L := fun L hL => by
    obtain ⟨w, hw⟩ := hcl3.classical L hL
    exact not_commutes_self_of_isClassicalMember3 hw
  rcases table_dispatch D hcl3.conjInvariant hO hnc hJ₁ hJ₂ hne hcomm ha hb hab hzb hcen with
    hT | hDb | hSp | hL | hU | hO7 | hOm
  · exact Or.inr (Or.inr (Or.inr (Or.inr hT)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ι, hfin, D, hz, hDb⟩)))
  · exact Or.inl (pspNbhdKind_sp4_iff.mpr ⟨ι, hfin, D, hz, hSp⟩)
  · exact Or.inr (Or.inl (pspNbhdKind_l4_iff.mpr ⟨ι, hfin, D, hz, hL⟩))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨ι, hfin, D, hz, hU⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨ι, hfin, D, hz, hO7⟩))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨ι, hfin, D, hz, hOm⟩))))

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
