module

public import CFSG.ClassicalInvolution.Q3.AE.Local

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def nyList : List (Wr 4) :=
  kList.flatMap fun k₁ => kStarList.flatMap fun k₂ => [k₁ * k₂, k₁ * k₂ * yQ, k₁ * k₂ * yQ * yQ]

theorem loc_conj_y : ∀ b : Wr 4, b * yQ * b⁻¹ ∈ nyList := by decide +kernel

theorem loc_cent : ∀ b : Wr 4, (∀ k ∈ kList, b * k * b⁻¹ = k) →
    (∀ k ∈ kStarList, b * k * b⁻¹ = k) → b = 1 ∨ b = zQ := by decide +kernel

theorem loc_twin_even : ∀ u : Fin 4 → ZMod 2, ∑ i, u i = 0 →
    (∀ k ∈ kList, ofVec u * k * (ofVec u)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofVec u * k * (ofVec u)⁻¹ ∈ kStarList) := by decide +kernel

theorem loc_twin_odd : ∀ u : Fin 4 → ZMod 2, ∑ i, u i = 1 →
    (∀ k ∈ kList, ofVec u * k * (ofVec u)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofVec u * k * (ofVec u)⁻¹ ∈ kList) := by decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
