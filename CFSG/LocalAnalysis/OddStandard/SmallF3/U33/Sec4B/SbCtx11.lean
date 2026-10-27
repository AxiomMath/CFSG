module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ASwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

namespace S4B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctxX_swap (ht2 : t * t = 1) : ctxX t (t * tau) x₁ x₂ = ctxX t tau x₁ x₂ := by
  have hτ : tau = t * (t * tau) := by rw [← mul_assoc, ht2, one_mul]
  apply le_antisymm
  · rw [ctxX, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.subset_closure (by simp)
  · rw [ctxX, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]
      have hmem : t * (t * tau) ∈ closure {t, t * tau, x₁ ^ 2, (x₁ * x₂) ^ 2} :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      rwa [← hτ] at hmem
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.subset_closure (by simp)

theorem ctxM_swap (ht2 : t * t = 1) : ctxM t (t * tau) x₁ x₂ = ctxM t tau x₁ x₂ := by
  rw [ctxM, ctxM, ctxX_swap ht2]

theorem fourGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : fourGrp x₁ x₂ ≤ L := by
  rw [fourGrp, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact (S4A.y_z_mem_L h).1
  · exact (S4A.y_z_mem_L h).2

theorem ttau_not_mem_union (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    t * tau ∉ t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) := by
  have hVL := fourGrp_le_L hc.toCtx0
  have hcomm : tau * t = t * tau :=
    S4A.mem_invCent_iff.mp (hc.toCtx0.le_invCent hc.tau_mem)
  rintro (⟨f, hf, h1⟩ | ⟨f, hf, h1⟩)
  · have hf' : f = tau := mul_left_cancel h1
    exact hc.tau_not_mem (hf' ▸ Subgroup.mem_sup_right (hVL hf))
  · have h2 : tau * f = tau * t := by rw [hcomm]; exact h1
    have hf' : f = t := mul_left_cancel h2
    exact S4A.t_not_mem_L hc.hyp (hf' ▸ hVL hf)

theorem false_of_tM_all (hc : Ctx10 t L S x₁ x₂ lam rho tau)
    (h : conjIn (ctxM t tau x₁ x₂) t =
      t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) ∪
        (t * tau) • (fourGrp x₁ x₂ : Set G)) : False := by
  obtain ⟨-, h8, -⟩ := S4A.ncard_tF_cases hc.toCtx hc.l44.1
  have hnot := ttau_not_mem_union hc.toCtx4
  have hsub : insert (t * tau) (t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G)) ⊆
      conjIn (ctxM t tau x₁ x₂) t := by
    rw [h]
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨1, (fourGrp x₁ x₂).one_mem, mul_one _⟩
    · exact Or.inl hx
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), h8] at hcard
  rcases hc.l410 with h4 | h8'
  · omega
  · omega

end S4B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctx11_exists (h411 : Lemma4_11Stmt) (h411c : Ctx11OfTMStmt) (hI : Sec4Inputs)
    (hG : Sec4Glob G) (hB : Sec4BInputs) (hc : Ctx10 t L S x₁ x₂ lam rho tau) :
    ∃ tau' : G, Ctx11 t L S x₁ x₂ lam rho tau' := by
  have hne : (conjIn (ctxM t tau x₁ x₂) t).ncard ≠ 4 := h411 hG hB hc
  obtain ⟨h4, -, -⟩ := S4A.ncard_tF_cases hc.toCtx hc.l44.1
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  rcases hc.l49.2 with h | h | h | h
  · exact absurd (by rw [h]; exact h4) hne
  · refine ⟨t * tau, h411c (ctx10_of_ctx4 hI hG (S4A.ctx4_swap hc.toCtx4)) ?_⟩
    rw [S4B.ctxM_swap ht2, h, show t * (t * tau) = tau by rw [← mul_assoc, ht2, one_mul]]
  · exact ⟨tau, h411c hc h⟩
  · exact (S4B.false_of_tM_all hc h).elim

end CFSG.OddStandard.SmallF3.HarrisU33
