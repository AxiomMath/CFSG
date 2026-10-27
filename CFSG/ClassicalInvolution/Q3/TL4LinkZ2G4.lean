module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4L
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4Sp
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4OC
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4U

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint


theorem gapOmegaSmall_of_certs :
    GapOmegaSmall := by
  intro W _ _ Φ K K' k k' σ hT N hNn hN hS
  rcases hS with hS | hS | hS | hS
  · obtain ⟨x, hx⟩ := G4.sPHyp_of_quotCenter hT N hN (Or.inr (Or.inl rfl)) hS
    exact G4.false_of_sPHyp_PSp hS hx
  · obtain ⟨x, hx⟩ := G4.sPHyp_of_quotCenter hT N hN (Or.inr (Or.inr (Or.inl rfl))) hS
    exact G4.false_of_sPHyp_PSU hS hx
  · obtain ⟨x, hx⟩ := G4.sPHyp_of_quotCenter hT N hN (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hS
    exact G4.false_of_sPHyp_POmegaOdd le_rfl hS hx
  · obtain ⟨x, hx⟩ :=
      G4.sPHyp_of_quotCenter hT N hN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hS
    exact G4.false_of_sPHyp_POmegaMinus4 hS hx

theorem gapOmegaL43_of_certs : GapOmegaL43 := by
  intro W _ _ Φ K K' k k' σ hT N hNn hN hS
  exact G4.l43_quotient hT N hN hS

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
