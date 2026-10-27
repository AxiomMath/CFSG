module

public import Certificates.Data.Kernel.EvenSporM22.HS08Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Level
public import CFSG.Certificates.Kernel.EvenSporM22.E32Sound
public import Certificates.Certificate25930

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check

theorem cover_of_JOK {L₀ : List Tab} (h : JOK L₀) :
    ∀ k, 2 ^ k ≤ 32 → ∃ L ∈ elemLevel s0Tabs k, ∀ l ∈ L, l ∈ L₀ := by
  obtain ⟨hlen, hnd, hid, hp⟩ := h
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[idTab], List.mem_singleton_self _, fun l hl => ?_⟩
    rw [List.mem_singleton.1 hl]
    exact hid
  | succ k ih =>
    intro hk
    have hk' : 2 ^ k ≤ 32 := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)) hk
    obtain ⟨L, hL, hsub⟩ := ih hk'
    have hLlen : L.length = 2 ^ k := length_of_mem_elemLevel s0Tabs k L hL
    have hlt : L.length < 32 := by
      rw [hLlen]
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)) hk
    have hx : ∃ x ∈ L₀, x ∉ L := by
      by_contra hc
      push Not at hc
      have h1 : L₀.toFinset ⊆ L.toFinset := fun x hx =>
        List.mem_toFinset.2 (hc x (List.mem_toFinset.1 hx))
      have h2 := Finset.card_le_card h1
      rw [List.toFinset_card_of_nodup hnd, hlen] at h2
      have h3 := List.toFinset_card_le L
      omega
    obtain ⟨x, hx0, hxL⟩ := hx
    have hxc : x ∈ extCands (invTabs s0Tabs) L := by
      rw [mem_extCands, invTabs, List.mem_filter, decide_eq_true_eq]
      exact ⟨⟨(hp x hx0).1, (hp x hx0).2.1⟩, hxL, fun z hz => ((hp x hx0).2.2 z (hsub z hz)).2⟩
    refine ⟨sortTabs (ext L x), mem_elemStep.2 ⟨L, hL, x, hxc, rfl⟩, fun l hl => ?_⟩
    rw [sortTabs, List.mem_mergeSort, ext, List.mem_append, List.mem_map] at hl
    rcases hl with hl | ⟨z, hz, rfl⟩
    · exact hsub l hl
    · exact ((hp x hx0).2.2 z (hsub z hz)).1

theorem sorted_of_mem_elemLevel_succ (T : List Tab) (k : Nat) {L : List Tab}
    (hL : L ∈ elemLevel T (k + 1)) : L.Pairwise tabR := by
  obtain ⟨L0, -, x, -, rfl⟩ := mem_elemStep.1 hL
  rw [sortTabs_eq, isortK_eq]
  exact List.pairwise_insertionSort _ _


theorem jTabs_eq_of_JOK {L₀ : List Tab} (hs : L₀.Pairwise tabR) (h : JOK L₀) : jTabs = L₀ := by
  have hc : CheckProp := of_decide_eq_true Certificates.certificate25930
  obtain ⟨L, hL, hsub⟩ := cover_of_JOK h 5 (by norm_num)
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hc.1
  have hLa : L = a := by
    rw [ha, List.mem_singleton] at hL
    exact hL
  have hj : jTabs = L := by
    rw [jTabs_eq, ha, hLa]
    rfl
  have hperm : jTabs.Perm L₀ := by
    refine List.Subperm.perm_of_length_le (List.Nodup.subperm hc.2.2.2.1 ?_) ?_
    · intro l hl
      rw [hj] at hl
      exact hsub l hl
    · rw [h.1, hc.2.2.1]
  have hjs : jTabs.Pairwise tabR := by
    rw [hj]
    exact sorted_of_mem_elemLevel_succ s0Tabs 4 hL
  exact hperm.eq_of_pairwise (fun a b _ _ h1 h2 => tabLE_antisymm a b h1 h2) hjs hs

theorem jLit_sorted : jLit.Pairwise tabR := by
  rw [jLit, isortK_eq]
  exact List.pairwise_insertionSort _ _

theorem jTabs_eq_jLit (h : JOK jLit) : jTabs = jLit := jTabs_eq_of_JOK jLit_sorted h

end CFSG.KC.EvenSporM22
