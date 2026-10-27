module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Perm

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

open Equiv
open CFSG.RankThree.PartTwo.Sec4.Item434F42 (wordElt enum_spec)

variable {n : ℕ}

theorem allDistinct_nodup {l : List (Array ℕ)} (h : allDistinct l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    have h1 : xs.contains x = false := h.1
    refine List.nodup_cons.2 ⟨fun hx => ?_, ih h.2⟩
    have h2 : xs.contains x = true := List.contains_iff_mem.2 hx
    rw [h1] at h2
    exact Bool.false_ne_true h2

theorem enumOK_sound {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {L : List (List ℕ)} (h : enumOK n (ws.map (swapsArr n)) L = true) :
    (∀ x : alternatingGroup (Fin n),
      x ∈ Subgroup.closure (gensFn n ws '' {k | k < ws.length}) ↔
        ∃ w ∈ L, wordElt (gensFn n ws) w = x) ∧
      Nat.card (Subgroup.closure (gensFn n ws '' {k | k < ws.length})) = L.length := by
  simp only [enumOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlet, hnil⟩, hcl⟩, hdis⟩ := h
  have hlet' : ∀ w ∈ L, ∀ l ∈ w, l < ws.length := by
    intro w hw l hl
    simpa using hlet w hw l hl
  refine enum_spec (g := gensFn n ws) (r := ws.length) (L := L) hlet'
    (List.contains_iff_mem.1 hnil) ?_ ?_
  · intro w hw k hk
    have hmem : wordArr n (ws.map (swapsArr n)) w ∈ L.map (wordArr n (ws.map (swapsArr n))) :=
      List.mem_map_of_mem hw
    have := hcl k (List.mem_range.2 (by simpa using hk)) _ hmem
    obtain ⟨w', hw', hw'eq⟩ := List.mem_map.1 (List.contains_iff_mem.1 this)
    refine ⟨w', hw', ?_⟩
    have e1 := wordArr_eq hv (hlet' w' hw')
    have e2 := wordArr_eq hv (hlet' w hw)
    have e3 := permArr_gensFn hk hv
    rw [e1, e2, e3, pmul_permArr] at hw'eq
    exact Subtype.ext (permArr_injective hw'eq)
  · have hnd := allDistinct_nodup hdis
    rw [List.map_congr_left (fun w hw => wordArr_eq hv (hlet' w hw))] at hnd
    have hmap : (L.map (wordElt (gensFn n ws))).map
        (fun x : alternatingGroup (Fin n) => permArr n (x : Perm (Fin n))) =
        L.map (fun w => permArr n ((wordElt (gensFn n ws) w : alternatingGroup (Fin n)) :
          Perm (Fin n))) := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap] at hnd
    exact List.Nodup.of_map _ hnd

theorem enumOK_letters {ws : List (List (ℕ × ℕ))} {L : List (List ℕ)}
    (h : enumOK n (ws.map (swapsArr n)) L = true) : ∀ w ∈ L, ∀ l ∈ w, l < ws.length := by
  simp only [enumOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro w hw l hl
  simpa using h.1.1.1 w hw l hl

theorem enumOK_nodup {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {L : List (List ℕ)} (h : enumOK n (ws.map (swapsArr n)) L = true) :
    (L.map (wordArr n (ws.map (swapsArr n)))).Nodup := by
  have h' := h
  simp only [enumOK, Bool.and_eq_true] at h'
  exact allDistinct_nodup h'.2

theorem enumOK_vals {ws : List (List (ℕ × ℕ))} (hv : ∀ w ∈ ws, swapsOK n w = true)
    {L : List (List ℕ)} (h : enumOK n (ws.map (swapsArr n)) L = true) (y : Array ℕ) :
    y ∈ L.map (wordArr n (ws.map (swapsArr n))) ↔
      ∃ x ∈ Subgroup.closure (gensFn n ws '' {k | k < ws.length}),
        permArr n (x : Perm (Fin n)) = y := by
  have hlet := enumOK_letters h
  have hsound := (enumOK_sound hv h).1
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    refine ⟨wordElt (gensFn n ws) w, (hsound _).2 ⟨w, hw, rfl⟩, ?_⟩
    exact (wordArr_eq hv (hlet w hw)).symm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (hsound x).1 hx
    exact List.mem_map.2 ⟨w, hw, wordArr_eq hv (hlet w hw)⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK.P12
