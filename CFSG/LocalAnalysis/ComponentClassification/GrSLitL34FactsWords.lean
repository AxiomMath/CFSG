module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def genS (j : ℕ) : Equiv.Perm (Fin 42) := if j = 0 then g₁ else if j = 1 then g₂ else g₃

@[expose] def genT (j : ℕ) : Tab := if j = 0 then g₁T else if j = 1 then g₂T else g₃T

@[expose] def wordPerm (w : List ℕ) : Equiv.Perm (Fin 42) := w.foldl (fun g j => g * genS j) 1

@[expose] def wordTab (w : List ℕ) : Tab := w.foldl (fun t j => comp 42 t (genT j)) (idTab 42)

@[expose] def wordSet (ws : List (List ℕ)) : Set (Equiv.Perm (Fin 42)) :=
  {g | ∃ w ∈ ws, wordPerm w = g}

@[expose] def wordTabs (ws : List (List ℕ)) : Array Tab := (ws.map wordTab).toArray

theorem tabRep_genT (j : ℕ) : TabRep (genT j) (genS j) := by
  unfold genT genS
  split_ifs
  · exact tabRep_g₁
  · exact tabRep_g₂
  · exact tabRep_g₃

theorem genS_mem (j : ℕ) : genS j ∈ S := by
  unfold genS
  split_ifs
  · exact g₁_mem_S
  · exact g₂_mem_S
  · exact g₃_mem_S

theorem tabRep_foldl (w : List ℕ) {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) :
    TabRep (w.foldl (fun t j => comp 42 t (genT j)) t) (w.foldl (fun g j => g * genS j) g) := by
  induction w generalizing t g with
  | nil => exact ht
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (ht.comp (tabRep_genT j))

theorem tabRep_wordTab (w : List ℕ) : TabRep (wordTab w) (wordPerm w) := by
  rw [wordTab, wordPerm]
  exact tabRep_foldl w (TabRep.idTab (n := 42))

theorem foldl_mem (w : List ℕ) {g : Equiv.Perm (Fin 42)} (hg : g ∈ S) :
    w.foldl (fun g j => g * genS j) g ∈ S := by
  induction w generalizing g with
  | nil => exact hg
  | cons j w ih => exact ih (S.mul_mem hg (genS_mem j))

theorem wordPerm_mem (w : List ℕ) : wordPerm w ∈ S := foldl_mem w S.one_mem

theorem wordSet_subset (ws : List (List ℕ)) : wordSet ws ⊆ S := by
  rintro _ ⟨w, -, rfl⟩
  exact wordPerm_mem w

theorem closure_wordSet_le (ws : List (List ℕ)) : Subgroup.closure (wordSet ws) ≤ S :=
  (Subgroup.closure_le S).2 (wordSet_subset ws)

theorem size_wordTabs (ws : List (List ℕ)) : (wordTabs ws).size = ws.length := by
  simp [wordTabs]

theorem wordTabs_getElem! (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    (wordTabs ws)[j]! = wordTab ws[j] := by
  rw [getElem!_pos (wordTabs ws) j (by rw [size_wordTabs]; exact hj)]
  simp [wordTabs]

theorem tabRep_wordTabs (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    TabRep (wordTabs ws)[j]! (wordPerm ws[j]) := by
  rw [wordTabs_getElem! ws hj]
  exact tabRep_wordTab _

theorem enumerates_wordClosure {ws : List (List ℕ)} {E : Enum}
    (h : enumOK 42 (wordTabs ws) E = true) :
    Enumerates (Subgroup.closure (wordSet ws)) E.tabs.toList := by
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) h
  · obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    exact ⟨j, by rw [size_wordTabs]; exact hj, tabRep_wordTabs ws hj⟩
  · rw [size_wordTabs] at hj
    exact ⟨_, ⟨ws[j], List.getElem_mem hj, rfl⟩, tabRep_wordTabs ws hj⟩

theorem mem_of_found_enum {H : Subgroup (Equiv.Perm (Fin 42))} {T : Array Tab}
    (hH : Enumerates H T.toList) {x : Tab} {g : Equiv.Perm (Fin 42)} (hx : TabRep x g)
    (h : found (indexOf T) T x = true) : g ∈ H := by
  obtain ⟨g', hg', hr⟩ := hH.sound _ (mem_of_found h)
  rwa [hx.perm_eq hr]

theorem mem_wordSet_iff {ws : List (List ℕ)} {g : Equiv.Perm (Fin 42)} :
    g ∈ wordSet ws ↔ ∃ j < ws.length, wordPerm ws[j]! = g := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    exact ⟨j, hj, by rw [getElem!_pos ws j hj]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ws[j], List.getElem_mem hj, by rw [getElem!_pos ws j hj]⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
