module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

@[expose] def e0 : Wr 4 := ofVec (vec4 [0])

theorem e0Prod : ∀ k ∈ kList ++ kStarList, k ≠ 1 → k ≠ zQ →
    (k * (e0 * k * e0)).perm = 1 ∧ ∃ π : Equiv.Perm (Fin 4),
      ∀ i, (k * (e0 * k * e0)).vec (π i) = w0.vec i := by
  decide +kernel

@[expose] def permEmb {n : ℕ} (ι : Fin 4 ↪ Fin n) (π : Equiv.Perm (Fin 4)) : Fin 4 ↪ Fin n :=
  π.toEmbedding.trans ι

theorem range_permEmb {n : ℕ} (ι : Fin 4 ↪ Fin n) (π : Equiv.Perm (Fin 4)) :
    Set.range (permEmb ι π) = Set.range ι := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨π i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨π.symm i, by simp [permEmb]⟩

theorem embed_eq_embed_permEmb {n : ℕ} (ι : Fin 4 ↪ Fin n) (π : Equiv.Perm (Fin 4)) (w : Wr 4)
    (hw : w.perm = 1) (hv : ∀ i, w.vec (π i) = w0.vec i) :
    embed (permEmb ι π) w0 = embed ι w := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      have : ι j = permEmb ι π (π.symm j) := by simp [permEmb]
      rw [this, embedVec_apply, ← this, embedVec_apply, ← hv (π.symm j)]
      simp
    · have hx' : x ∉ Set.range (permEmb ι π) := by rwa [range_permEmb]
      rw [embedVec_of_not_mem _ _ hx, embedVec_of_not_mem _ _ hx']
  · rw [embed_perm, embed_perm, hw]
    have h1 : (w0.perm : Equiv.Perm (Fin 4)) = 1 := rfl
    rw [h1, embedPerm_one, embedPerm_one]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod
