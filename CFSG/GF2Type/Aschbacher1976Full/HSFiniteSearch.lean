module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteWlog

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

@[expose] def SearchOk (V reps l1 l2 : List (Perm (Fin 6))) : Prop :=
  (∀ a ∈ c2T, (∀ v ∈ V.map tab, CompatT a v) → a ∈ (mk V reps).map tab) ∧
  (∀ O ∈ reps.map (fun r => (orbit V r).map tab), ∀ t ∈ O, ∀ t' ∈ O,
    t = t' ∨ ∃ v ∈ V.map tab, mulT v t = mulT t' v) ∧
  (∀ ls ∈ reps.sublists, GoodT ((mk V ls).map tab) → ls = [] ∨ ls = l1 ∨ ls = l2)

theorem orbit_subset_of_mem {V : List (Perm (Fin 6))} {reps : List (Perm (Fin 6))}
    (h2 : ∀ O ∈ reps.map (fun r => (orbit V r).map tab), ∀ t ∈ O, ∀ t' ∈ O,
      t = t' ∨ ∃ v ∈ V.map tab, mulT v t = mulT t' v)
    {D : Set (Perm (Fin 6))} (hconj : ∀ s ∈ D, ∀ t ∈ D, s * t * s⁻¹ ∈ D)
    (hV : ∀ v ∈ V, v ∈ D) {r t₀ : Perm (Fin 6)} (hr : r ∈ reps) (ht₀ : t₀ ∈ orbit V r)
    (hD : t₀ ∈ D) : ∀ t' ∈ orbit V r, t' ∈ D := by
  intro t' ht'
  have hO : (orbit V r).map tab ∈ reps.map (fun r => (orbit V r).map tab) :=
    List.mem_map_of_mem hr
  rcases h2 _ hO (tab t₀) (List.mem_map_of_mem ht₀) (tab t') (List.mem_map_of_mem ht') with
    h | ⟨vt, hvt, h⟩
  · rwa [← tab_injective h]
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hvt
    rw [← conj_eq_of_mulT h]
    exact hconj v (hV v hv) t₀ hD

theorem search_generic {V reps l1 l2 : List (Perm (Fin 6))} (h : SearchOk V reps l1 l2)
    (D : Set (Perm (Fin 6))) (hc2 : ∀ s ∈ D, tab s ∈ c2T)
    (hconj : ∀ s ∈ D, ∀ t ∈ D, s * t * s⁻¹ ∈ D) (hcompat : ∀ s ∈ D, ∀ t ∈ D, Compat s t)
    (hV : ∀ v ∈ V, v ∈ D) :
    ∃ ls, (ls = [] ∨ ls = l1 ∨ ls = l2) ∧ ∀ s, s ∈ D ↔ s ∈ mk V ls := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  set ls := reps.filter (fun r => decide (∀ t ∈ orbit V r, t ∈ D)) with hls
  have hmem : ∀ s, s ∈ D ↔ s ∈ mk V ls := by
    intro s
    constructor
    · intro hs
      have hs' : tab s ∈ (mk V reps).map tab := by
        refine h1 _ (hc2 s hs) fun a ha => ?_
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
        exact (compat_iff s v).1 (hcompat s hs v (hV v hv))
      rcases mem_mk.1 (mem_map_tab_iff.1 hs') with hsV | ⟨r, hr, hso⟩
      · exact mem_mk.2 (Or.inl hsV)
      · refine mem_mk.2 (Or.inr ⟨r, ?_, hso⟩)
        simp only [hls, List.mem_filter, decide_eq_true_eq]
        exact ⟨hr, orbit_subset_of_mem h2 hconj hV hr hso hs⟩
    · intro hs
      rcases mem_mk.1 hs with hsV | ⟨r, hr, hso⟩
      · exact hV s hsV
      · simp only [hls, List.mem_filter, decide_eq_true_eq] at hr
        exact hr.2 s hso
  refine ⟨ls, h3 ls (List.mem_sublists.2 (List.filter_sublist)) ?_, hmem⟩
  rw [← good_iff]
  refine ⟨fun s hs t ht => hcompat s ((hmem s).2 hs) t ((hmem t).2 ht), fun s hs t ht => ?_⟩
  exact (hmem _).1 (hconj s ((hmem s).2 hs) t ((hmem t).2 ht))

@[expose] def VA : List (Perm (Fin 6)) := [dt 0 1 2 3, dt 0 1 4 5, dt 2 3 4 5]

@[expose] def repsA : List (Perm (Fin 6)) :=
  [dt 1 2 3 4, dt 1 2 3 5, dt 1 4 3 5, dt 1 4 2 5, dt 0 2 1 4, dt 0 2 1 5]

@[expose] def selA1 : List (Perm (Fin 6)) := [dt 1 2 3 4, dt 1 4 3 5, dt 0 2 1 4]

@[expose] def selA2 : List (Perm (Fin 6)) := [dt 1 2 3 5, dt 1 4 2 5, dt 0 2 1 5]

theorem searchOk_A : SearchOk VA repsA selA1 selA2 := by
  unfold SearchOk
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def VB : List (Perm (Fin 6)) := [dt 0 1 2 3, dt 0 2 1 3, dt 0 3 1 2]

@[expose] def repsB : List (Perm (Fin 6)) :=
  [dt 1 2 3 4, dt 1 2 3 5, dt 1 3 2 4, dt 1 3 2 5, dt 1 4 2 3, dt 1 5 2 3]

@[expose] def selB1 : List (Perm (Fin 6)) := [dt 1 2 3 4, dt 1 3 2 4, dt 1 4 2 3]

@[expose] def selB2 : List (Perm (Fin 6)) := [dt 1 2 3 5, dt 1 3 2 5, dt 1 5 2 3]

theorem searchOk_B : SearchOk VB repsB selB1 selB2 := by
  unfold SearchOk
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.GF2Type.Aschbacher1976Full.HS.Six
