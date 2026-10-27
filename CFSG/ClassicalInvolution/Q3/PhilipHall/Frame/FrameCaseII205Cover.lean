module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205CNbr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D


theorem frameXCover_of_invConj (h : FrameAInvConj) : FrameXCover := by
  intro G _ _ _ K K' J S R R' W V z t d ρ _ hρt L hL
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  set Y := X ⊔ conjSub ρ⁻¹ X ⊔ Subgroup.zpowers ρ with hYdef
  have hXY : X ≤ Y := le_trans le_sup_left le_sup_left
  have hKX : K ≤ X := le_sec20X_left
  have hK'X : K' ≤ X := le_sec20X_right
  have hKY : K ≤ Y := hKX.trans hXY
  have hK'Y : K' ≤ Y := hK'X.trans hXY
  have hsig : ∀ M, Relation.ReflTransGen (aGraphAdj (CoreAssembly.conjClass K)) K M →
      ∃ y ∈ Y, M = conjSub y K ∨ M = conjSub y K' := by
    intro M hM
    induction hM with
    | refl => exact ⟨1, Subgroup.one_mem Y, Or.inl (conjSub_one K).symm⟩
    | @tail M₁ M₂ _ hadj ih =>
      obtain ⟨y, hy, hM₁⟩ := ih
      have hB : conjSub y⁻¹ M₁ = K ∨ conjSub y⁻¹ M₁ = K' := by
        rcases hM₁ with h1 | h1
        · exact Or.inl (by rw [h1, conjSub_inv_conjSub])
        · exact Or.inr (by rw [h1, conjSub_inv_conjSub])
      have hadj' := aGraphAdj_conj' d.hyp.conjInvariant hadj y⁻¹
      obtain ⟨w, hw, hMw⟩ := frameANbr_mem_cover h d hρt hB hadj'
      refine ⟨y * w, Subgroup.mul_mem Y hy hw, ?_⟩
      rcases hMw with h2 | h2
      · exact Or.inl (by rw [conjSub_mul, ← h2, conjSub_conjSub_inv])
      · exact Or.inr (by rw [conjSub_mul, ← h2, conjSub_conjSub_inv])
  have hconj : ∀ y ∈ Y, ∀ B : Subgroup G, B ≤ Y → conjSub y B ≤ Y := by
    intro y hy B hB x hx
    rw [mem_conjSub_iff] at hx
    have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    have hmem := Subgroup.mul_mem Y (Subgroup.mul_mem Y hy (hB hx)) (Subgroup.inv_mem Y hy)
    rwa [e] at hmem
  obtain ⟨y, hy, hLy⟩ := hsig L hL
  rcases hLy with h1 | h1
  · rw [h1]
    exact hconj y hy K hKY
  · rw [h1]
    exact hconj y hy K' hK'Y

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
