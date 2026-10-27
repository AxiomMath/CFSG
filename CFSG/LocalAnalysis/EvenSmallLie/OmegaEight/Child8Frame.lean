module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Defs

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

@[expose] def planeWords : List (Finset (Fin 8) × List (Fin 2)) :=
  [({0, 1, 2, 3}, []), ({0, 1, 4, 5}, [0]), ({0, 1, 6, 7}, [0, 0, 0]),
    ({0, 2, 4, 6}, [0, 0, 0, 0, 0, 0]), ({0, 2, 5, 7}, [0, 0]), ({0, 3, 4, 7}, [0, 0, 0, 0, 0]),
    ({0, 3, 5, 6}, [0, 0, 0, 0]), ({1, 2, 4, 7}, [0, 0, 0, 0, 0, 1]),
    ({1, 2, 5, 6}, [0, 0, 0, 0, 1]), ({1, 3, 4, 6}, [0, 0, 1, 0, 0, 0]),
    ({1, 3, 5, 7}, [0, 0, 1]), ({2, 3, 4, 5}, [0, 0, 1, 0, 0, 0, 0]),
    ({2, 3, 6, 7}, [0, 0, 1, 0, 0]), ({4, 5, 6, 7}, [0, 0, 1, 0])]

theorem plane_words : ∀ B ∈ frameBlocks, ∃ p ∈ planeWords, p.1 = B ∧
    permVec (frameWord p.2) (blockVec B) = blockVec {0, 1, 2, 3} := by
  decide +kernel

namespace Child8Weyl

variable {W : Type} [Group W] [Finite W] (M : Child8Weyl W)

@[expose] def realized : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∃ w ∈ M.Wp, ∀ v : FrameVec,
    w * M.ιE1 (Multiplicative.ofAdd v) * w⁻¹ = M.ιE1 (Multiplicative.ofAdd (permVec σ v))}
  mul_mem' := by
    rintro σ τ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, fun v => ?_⟩
    rw [permVec_mul, ← h₁, ← h₂]
    group
  one_mem' := ⟨1, one_mem _, fun v => by rw [permVec_one]; group⟩
  inv_mem' := by
    rintro σ ⟨w, hw, h⟩
    refine ⟨w⁻¹, inv_mem hw, fun v => ?_⟩
    have h1 := h (permVec σ⁻¹ v)
    rw [permVec_permVec_inv] at h1
    rw [← h1]
    group

theorem closure_le_realized : closure frameGens ≤ M.realized :=
  (closure_le _).2 M.frame_gens

theorem frameWord_mem_realized (w : List (Fin 2)) : frameWord w ∈ M.realized :=
  M.closure_le_realized (frameWord_mem_closure w)

theorem x₀_mem_E : M.x₀ ∈ M.ιE.range := by
  rw [M.x₀_eq]
  exact M.reps_mem _ (by simp)

theorem exists_conj_plane {B : Finset (Fin 8)} (hB : B ∈ frameBlocks) :
    ∃ w ∈ M.Wp, w * M.ιE1 (Multiplicative.ofAdd (blockVec B)) * w⁻¹ = M.x₀ := by
  obtain ⟨p, -, rfl, hp⟩ := plane_words B hB
  obtain ⟨w, hw, h⟩ := M.frameWord_mem_realized p.2
  exact ⟨w, hw, by rw [h, hp, M.x₀_eq]⟩

theorem exists_conj_mem_E {v : FrameVec}
    (hcls : frameCls v = 2 ∨ frameCls v = 4 ∨ frameCls v = 7) :
    ∃ w ∈ M.Wp, w * M.ιE1 (Multiplicative.ofAdd v) * w⁻¹ ∈ M.ιE.range := by
  set Y : Set FrameVec :=
    {u | ∃ w ∈ M.Wp, w * M.ιE1 (Multiplicative.ofAdd u) * w⁻¹ ∈ M.ιE.range} with hY
  have hYcl : ∀ σ ∈ closure frameGens, ∀ u ∈ Y, permVec σ u ∈ Y := by
    rintro σ hσ u ⟨w, hw, hu⟩
    obtain ⟨r, hr, h⟩ := M.closure_le_realized hσ
    refine ⟨w * r⁻¹, mul_mem hw (inv_mem hr), ?_⟩
    rw [← h u]
    convert hu using 1
    group
  have hrep : ∀ u ∈ ({frameE 0 + frameE 1, blockVec {0, 1, 2, 3},
      frameZ + frameE 0 + frameE 1} : Set FrameVec), u ∈ Y := fun u hu =>
    ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact M.reps_mem u hu⟩
  rcases hcls with h | h | h
  · exact mem_of_frameCls_eq hYcl (u := frameE 0 + frameE 1) (by rw [h]; decide) (by decide)
      (by decide) (by decide) (hrep _ (by simp))
  · obtain ⟨B, hB, rfl⟩ := (frameCls_eq_four_iff v).1 h
    obtain ⟨w, hw, hwx⟩ := M.exists_conj_plane hB
    exact ⟨w, hw, hwx ▸ M.x₀_mem_E⟩
  · exact mem_of_frameCls_eq hYcl (u := frameZ + frameE 0 + frameE 1) (by rw [h]; decide)
      (by decide) (by decide) (by decide) (hrep _ (by simp))

end Child8Weyl

end CFSG.EvenSmallLie.OmegaEight.Child8
