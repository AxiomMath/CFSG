module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319ValX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

private theorem mu_apply (p : FzUT) (a b c : ZMod 2) :
    D.mu (p, (a, b, c)) = (D.φ.symm p : G) * t ^ a.val * tau ^ b.val * lam ^ c.val := rfl

private theorem isQ8 {a b : FzElt} (h : FzQ8 (fzMulC D.cT D.cS D.cL) fzOneC a b) :
    IsQ8Pair (D.mu a) (D.mu b) := by
  obtain ⟨h4, hsq, hconj, hne⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := congrArg D.mu h4
    rw [D.mu_mul, D.mu_mul, D.mu_one] at h1
    calc D.mu a ^ 4 = (D.mu a * D.mu a) * (D.mu a * D.mu a) := by simp [pow_succ, mul_assoc]
      _ = 1 := h1
  · have h1 := congrArg D.mu hsq
    rw [D.mu_mul, D.mu_mul] at h1
    rw [pow_two, pow_two]
    exact h1
  · have h1 := congrArg D.mu hconj
    rw [D.mu_mul, D.mu_mul] at h1
    have h2 : D.mu b * D.mu a = (D.mu a)⁻¹ * D.mu b := by
      calc D.mu b * D.mu a = (D.mu a)⁻¹ * (D.mu a * D.mu b * D.mu a) := by group
        _ = (D.mu a)⁻¹ * D.mu b := by rw [h1]
    calc D.mu b * D.mu a * (D.mu b)⁻¹ = (D.mu a)⁻¹ * D.mu b * (D.mu b)⁻¹ := by rw [h2]
      _ = (D.mu a)⁻¹ := by group
  · intro h1
    apply hne
    apply D.mu_injective
    rw [D.mu_mul, D.mu_one]
    rw [pow_two] at h1
    exact h1

private theorem comm_of {a b : FzElt}
    (h : fzMulC D.cT D.cS D.cL a b = fzMulC D.cT D.cS D.cL b a) :
    Commute (D.mu a) (D.mu b) := by
  have h1 := congrArg D.mu h
  rw [D.mu_mul, D.mu_mul] at h1
  exact h1

private theorem shape_aux {a11 a12 a21 a22 a31 a32 y : FzElt} {x₁ x₂ : G}
    (hs : FzShapeAt (fzMulC D.cT D.cS D.cL) fzOneC a11 a12 a21 a22 a31 a32 y)
    (e11 : D.mu a11 = x₁ * t) (e21 : D.mu a21 = x₂ * t)
    (e31 : D.mu a31 = (x₁ * x₂)⁻¹ * t) (ey : D.mu y = lam) :
    FzSpShape t x₁ x₂ lam T (D.mu a12) (D.mu a22) (D.mu a32) := by
  have hlam2 : lam * lam = 1 := by
    have h1 := congrArg D.mu hs.y_sq
    rw [D.mu_mul, D.mu_one, ey] at h1
    exact h1
  have hli : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := D.isQ8 hs.quat₁
    rw [e11] at h1
    exact h1
  · have h1 := D.isQ8 hs.quat₂
    rw [e21] at h1
    exact h1
  · have h1 := D.isQ8 hs.quat₃
    rw [e31] at h1
    exact h1
  · have h1 := congrArg D.mu hs.sq_eq
    rw [D.mu_mul, D.mu_mul, D.mu_mul, D.mu_mul, e11, e21, e31] at h1
    rw [pow_two, pow_two, pow_two]
    exact h1
  · rw [← e11, ← e21]
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      exact D.comm_of (hs.comm₁₂ _ (by simp) _ (by simp))
  · rw [← e11, ← e31]
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      exact D.comm_of (hs.comm₁₃ _ (by simp) _ (by simp))
  · rw [← e21, ← e31]
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      exact D.comm_of (hs.comm₂₃ _ (by simp) _ (by simp))
  · rw [pow_two]
    exact hlam2
  · have h1 := congrArg D.mu hs.y_a11
    rw [D.mu_mul, D.mu_mul, ey, e11, e21] at h1
    rw [hli]
    exact h1
  · have h1 := congrArg D.mu hs.y_a12
    rw [D.mu_mul, D.mu_mul, ey] at h1
    rw [hli]
    exact h1
  · have h1 := congrArg D.mu hs.y_a31
    have h2 := congrArg D.mu hs.y_a32
    rw [D.mu_mul, D.mu_mul, ey, e31] at h1
    rw [D.mu_mul, D.mu_mul, ey] at h2
    exact ⟨h1, h2⟩
  · apply le_antisymm
    · have hgen : ∀ x : FzElt, D.mu x ∈ Subgroup.closure
          ({x₁ * t, D.mu a12, x₂ * t, D.mu a22, (x₁ * x₂)⁻¹ * t, D.mu a32, lam} : Set G) := by
        intro x
        have hr := hs.gen x
        induction hr with
        | one =>
          rw [D.mu_one]
          exact one_mem _
        | @gen g' hg' =>
          apply Subgroup.subset_closure
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
          rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [e11]; simp
          · simp
          · rw [e21]; simp
          · simp
          · rw [e31]; simp
          · simp
          · rw [ey]; simp
        | mul ha hb iha ihb =>
          rw [D.mu_mul]
          exact mul_mem iha ihb
      intro g hg
      obtain ⟨x, rfl⟩ := D.mu_surj hg
      exact hgen x
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e11]; exact D.mu_mem _
      · exact D.mu_mem _
      · rw [← e21]; exact D.mu_mem _
      · exact D.mu_mem _
      · rw [← e31]; exact D.mu_mem _
      · exact D.mu_mem _
      · exact D.lam_mem
  · rw [D.str.card_T]
    norm_num

theorem shape_sp {x₁ x₂ : G} (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) (hl : lam * x₁ * lam⁻¹ = x₂)
    (h : FzShape D.cT D.cS D.cL (D.φ ⟨x₁, D.pf.EP hx₁⟩)) :
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T a₁₂ a₂₂ a₃₂ := by
  obtain ⟨r₁, r₃, hs⟩ := h
  have h1v : (1 : ZMod 2).val = 1 := by decide
  have h0v : (0 : ZMod 2).val = 0 := by decide
  have hL : (D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩) = D.φ ⟨x₂, D.pf.EP hx₂⟩ := D.cL_x hx₁ hx₂ hl
  have e11 : D.mu (D.φ ⟨x₁, D.pf.EP hx₁⟩, (1, 0, 0)) = x₁ * t := by
    rw [mu_apply, MulEquiv.symm_apply_apply, h1v, h0v]
    simp
  have e21 : D.mu ((D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩), (1, 0, 0)) = x₂ * t := by
    rw [mu_apply, hL, MulEquiv.symm_apply_apply, h1v, h0v]
    simp
  have e31 : D.mu (((D.φ ⟨x₁, D.pf.EP hx₁⟩) * (D.cL) (D.φ ⟨x₁, D.pf.EP hx₁⟩))⁻¹, (1, 0, 0))
      = (x₁ * x₂)⁻¹ * t := by
    rw [mu_apply, hL, h1v, h0v, ← map_mul, map_inv, MulEquiv.symm_apply_apply]
    simp
  have ey : D.mu ((1 : FzUT), ((0 : ZMod 2), (0 : ZMod 2), (1 : ZMod 2))) = lam := by
    rw [mu_apply, h1v, h0v]
    simp
  exact ⟨_, _, _, D.shape_aux hs e11 e21 e31 ey⟩

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
