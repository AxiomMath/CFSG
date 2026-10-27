module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section Comb

open Classical

variable {m : ℕ} {I : Set (Fin m)}

theorem blk_interval {p : Fin (m + 1)} (hne : (nodesOf (blkSet I p)).Nonempty) :
    ∃ a b : ℕ, a < b ∧ b ≤ m ∧ (∀ j : Fin m, j ∈ nodesOf (blkSet I p) ↔ a ≤ j.val ∧ j.val < b) ∧
      (Fin.last m ∈ blkSet I p ↔ b = m) := by
  obtain ⟨k, hk⟩ := hne
  set B := blkSet I p with hB
  have hne' : (B.image Fin.val).Nonempty := ⟨_, Finset.mem_image_of_mem _ hk.1⟩
  obtain ⟨qa, hqaB, hqa⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne')
  obtain ⟨qb, hqbB, hqb⟩ := Finset.mem_image.1 (Finset.max'_mem _ hne')
  set a := (B.image Fin.val).min' hne' with ha
  set b := (B.image Fin.val).max' hne' with hb
  have hle : ∀ q ∈ B, a ≤ q.val ∧ q.val ≤ b := fun q hq =>
    ⟨Finset.min'_le _ _ (Finset.mem_image_of_mem _ hq),
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hq)⟩
  have hmem : ∀ q : Fin (m + 1), q ∈ B ↔ a ≤ q.val ∧ q.val ≤ b := by
    intro q
    refine ⟨hle q, fun ⟨h1, h2⟩ => ?_⟩
    exact blkSet_convex hqaB hqbB (by rw [Fin.le_def, hqa]; exact h1)
      (by rw [Fin.le_def, hqb]; exact h2)
  have hk1 := hle _ hk.1
  have hk2 := hle _ hk.2
  simp only [Fin.val_castSucc, Fin.val_succ] at hk1 hk2
  refine ⟨a, b, by omega, by have := qb.isLt; omega, fun j => ?_, ?_⟩
  · show j.castSucc ∈ B ∧ j.succ ∈ B ↔ _
    rw [hmem, hmem]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · rw [hmem]
    simp only [Fin.val_last]
    have := qb.isLt
    omega

theorem nodes_nonadj {p q : Fin (m + 1)} (hpq : blkSet I p ≠ blkSet I q) {i j : Fin m}
    (hi : i ∈ nodesOf (blkSet I p)) (hj : j ∈ nodesOf (blkSet I q)) :
    i ≠ j ∧ ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  have hd := disjoint_blkSet hpq
  rw [Finset.disjoint_left] at hd
  refine ⟨fun h => hd hi.1 (h ▸ hj.1), ?_⟩
  rintro (h | h)
  · exact hd hi.2 (by
      have : j.castSucc = i.succ := Fin.ext (by simp [h])
      rw [← this]; exact hj.1)
  · exact hd hi.1 (by
      have : i.castSucc = j.succ := Fin.ext (by simp [h])
      rw [this]; exact hj.2)

end Comb

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
