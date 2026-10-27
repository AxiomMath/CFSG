module

public import Certificates.Data.Kernel.SolMaxSixGenK
public import CFSG.Certificates.Kernel.JordanReach

public section

namespace CFSG.ComponentClassification.SolMax.SixGen

open Equiv Subgroup

theorem evW_mem {gs : List (Perm (Fin 9))} {G : Subgroup (Perm (Fin 9))} (hgs : ∀ g ∈ gs, g ∈ G)
    (w : List ℕ) : evW gs w ∈ G := by
  unfold evW
  refine G.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[i]? with
  | none => exact G.one_mem
  | some g => exact hgs g (List.mem_of_getElem? h)

theorem permOf_mem_alternatingGroup {l : Swaps} (h : evenSwapsK l = true) :
    permOf l ∈ alternatingGroup (Fin 9) := by
  unfold evenSwapsK at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  unfold permOf
  rw [Perm.prod_list_swap_mem_alternatingGroup_iff_even_length]
  · rw [List.length_map, Nat.even_iff]
    exact h.1
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact ⟨p.1, p.2, by simpa using h.2 p hp, rfl⟩

theorem closure_eq_alternatingGroup_of_entryWitK {e : Swaps × List Swaps} {T S : List (List ℕ)}
    {C : List ℕ} (h : entryWitK e T S C = true) :
    closure {a | ∃ l ∈ e.2, a = permOf l} = alternatingGroup (Fin 9) := by
  unfold entryWitK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hev⟩, hr⟩ := h
  set G := closure {a | ∃ l ∈ e.2, a = permOf l} with hG
  have hgs : ∀ g ∈ e.2.map permOf, g ∈ G := fun g hg => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
    exact subset_closure ⟨l, hl, rfl⟩
  unfold reachK at hr
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨ht, hs⟩, hc⟩ := hr
  refine le_antisymm ?_ ?_
  · rw [closure_le]
    rintro a ⟨l, hl, rfl⟩
    exact permOf_mem_alternatingGroup (List.all_eq_true.1 hev l hl)
  · refine CFSG.KC.JordanReach.alternatingGroup_le_of_reach (n := 7) (G := G)
      (fun q => evW (e.2.map permOf) (T.getD q.val []))
      (fun q => evW (e.2.map permOf) (S.getD q.val []))
      (fun q => ⟨evW_mem hgs _, ht q⟩) (fun q hq => ?_) (evW_mem hgs C)
      (card_support_eq_three_iff.1 hc)
    rcases hs q with h0 | h1
    · exact absurd h0 hq
    · exact ⟨evW_mem hgs _, h1.1, h1.2⟩

end CFSG.ComponentClassification.SolMax.SixGen

end
