module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable

theorem normalClosure_filter_ne_nil {m : ℕ} (ws : List (List (Fin m × Bool))) :
    Subgroup.normalClosure {r : FreeGroup (Fin m) | r ∈ (ws.filter (· ≠ [])).map FreeGroup.mk} =
      Subgroup.normalClosure {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} := by
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_filter] at hr ⊢
    obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hr
    exact ⟨w, hw, rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    by_cases h : w = []
    · subst h
      rw [← FreeGroup.one_eq_mk]
      exact one_mem _
    · apply Subgroup.subset_normalClosure
      simp only [Set.mem_setOf_eq, List.mem_map, List.mem_filter]
      exact ⟨w, ⟨hw, by simpa using h⟩, rfl⟩

theorem PG_filter_ne_nil {m : ℕ} (ws : List (List (Fin m × Bool))) :
    PG m (ws.filter (· ≠ [])) = PG m ws := by
  unfold PG PresentedGroup
  rw [normalClosure_filter_ne_nil]

theorem PG_congr_mem {m : ℕ} {ws ws' : List (List (Fin m × Bool))} (h : ∀ w, w ∈ ws ↔ w ∈ ws') :
    PG m ws = PG m ws' := by
  have e : {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} =
      {r : FreeGroup (Fin m) | r ∈ ws'.map FreeGroup.mk} := by
    ext r
    simp only [Set.mem_setOf_eq, List.mem_map, h]
  unfold PG
  rw [e]

end CFSG.KC.MiscCoset
