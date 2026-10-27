module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameKit

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ} {I : FIdx}

theorem a1_mem_S (fr : SFrame Γ) : fr.a₁ ∈ fr.S := subset_closure (by simp)

theorem b1_mem_S (fr : SFrame Γ) : fr.b₁ ∈ fr.S := subset_closure (by simp)

theorem a2_mem_S (fr : SFrame Γ) : fr.a₂ ∈ fr.S := subset_closure (by simp)

theorem b2_mem_S (fr : SFrame Γ) : fr.b₂ ∈ fr.S := subset_closure (by simp)

theorem z_mem_S (fr : SFrame Γ) : fr.z ∈ fr.S := by
  unfold SFrame.z
  exact pow_mem (b1_mem_S fr) 2

theorem E_le_S (fr : SFrame Γ) : fr.E ≤ fr.S := by
  unfold SFrame.E
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mul_mem (b1_mem_S fr) (b2_mem_S fr)
  · exact mul_mem (mul_mem (a1_mem_S fr) (b1_mem_S fr)) (a2_mem_S fr)
  · exact z_mem_S fr

theorem F_le_S (fr : SFrame Γ) : fr.F ≤ fr.S := by
  unfold SFrame.F
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mul_mem (a1_mem_S fr) (a2_mem_S fr)
  · exact mul_mem (b1_mem_S fr) (b2_mem_S fr)
  · exact z_mem_S fr

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
