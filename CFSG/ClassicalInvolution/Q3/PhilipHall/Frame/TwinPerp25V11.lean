module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V10
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V7

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance



theorem _root_.CFSG.ClassicalInvolution.Q8P.Asc77.P25R.p25_ae5Excl_proved : P25_AE5Excl := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad' hTaz hae
  obtain ⟨ha2, ha1, haz⟩ := cA_pair_facts hyp h4 hcl hbad
  obtain ⟨hzA, hz2, hz1⟩ := z_facts hyp
  have haA : a ∈ cA S R R' := hcl ▸ Subgroup.subset_closure (by simp)
  have hza : a * z = z * a := hyp.hzS a haA.1
  have hazA : a * z ∈ cA S R R' := Subgroup.mul_mem _ haA hzA
  have haz2 : (a * z) * (a * z) = 1 := by
    calc (a * z) * (a * z) = a * (z * a) * z := by simp only [mul_assoc]
      _ = a * (a * z) * z := by rw [← hza]
      _ = (a * a) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [ha2, hz2, one_mul]
  have haz1 : a * z ≠ 1 := by
    intro hh
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left hh
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hz2)
  have hcl' : Subgroup.closure {a * z, z} = cA S R R' := (closure_az_pair hz2).trans hcl
  have Λ₁ : Lay Ω K K' W S R R' z t u₁ u₂ a := ⟨hyp, haA, ha2, ha1, hbad, TwinThmE.t4Supply_proved⟩
  have Λ₂ : Lay Ω K K' W S R R' z t u₁ u₂ (a * z) :=
    ⟨hyp, hazA, haz2, haz1, hbad', TwinThmE.t4Supply_proved⟩
  obtain ⟨A₁⟩ := AE5Layer.of_lay Λ₁ hae
  rcases hTaz with ⟨hno, h5 | h6⟩ | hae'
  · exact caseB Λ₁ Λ₂ (mul_z_z hz2) A₁ hno h5
  · exact not_layerLie6 hyp h4 hcl' hbad' TwinThmE.t4Supply_proved hno h6
  · obtain ⟨A₂⟩ := AE5Layer.of_lay Λ₂ hae'
    exact caseC Λ₁ Λ₂ (mul_z_z hz2) A₁ A₂

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
