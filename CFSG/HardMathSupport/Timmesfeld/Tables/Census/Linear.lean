module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Perm
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv Matrix CFSG.Open

variable {K : Type} [Field K]

theorem permGL_mem_SL {n : ℕ} {σ : Perm (Fin n)} (h : Perm.sign σ = 1) :
    permGL n K σ ∈ StatedSL n K := by
  refine Subgroup.subset_closure ?_
  rw [Set.mem_setOf_eq, det_permGL, h]
  simp

theorem permGL_mem_SU {n q : ℕ} (hq : q ≠ 0) {σ : Perm (Fin n)} (h : Perm.sign σ = 1) :
    permGL n K σ ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [det_permGL, h]
    simp
  · rw [coe_permGL]
    have h1 : ((σ⁻¹.permMatrix K).map (· ^ q)) = σ⁻¹.permMatrix K := by
      ext i j
      simp only [Matrix.map_apply, Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp [hq]
    rw [h1, transpose_permMatrix, ← permMatrix_mul]
    simp

theorem threeTwoWitness_psl {n : ℕ} (hn : 4 ≤ n) :
    ThreeTwoWitness (StatedProj (StatedSL n K)) :=
  threeTwoWitness_statedProj_perm hn fun _ h => permGL_mem_SL h

theorem threeTwoWitness_psu {n q : ℕ} (hn : 4 ≤ n) (hq : q ≠ 0) :
    ThreeTwoWitness (StatedProj (StatedSU n q K)) :=
  threeTwoWitness_statedProj_perm hn fun _ h => permGL_mem_SU hq h

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
