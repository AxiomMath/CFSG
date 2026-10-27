module

public import CFSG.Certificates.Kernel.J4TreeNode.W
public import Certificates.Data.Kernel.J4TreeNodeChunk

public section

namespace CFSG.KC.J4TreeN

open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node CFSG.ASVolI

section Glue


theorem not_contains {k : ℕ} {l : List ℕ} (h : k ∉ l) : l.contains k = false := by
  cases hh : l.contains k
  · rfl
  · exact absurd (List.mem_of_elem_eq_true hh) h

theorem chunkNode_sound {T : Tabs} {c : ℕ} {R : ℕ → NRec} {j : ℕ}
    (h : chunkNodeOK T c R j = true) (h1 : 1 ≤ 100 * c + j) (hN : 100 * c + j ≤ treeN)
    (ht : 100 * c + j ∉ treeTopIds) : nodeChk T (100 * c + j) (R j) = true := by
  unfold chunkNodeOK at h
  have e1 : (100 * c + j == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  have e2 : Nat.blt treeN (100 * c + j) = false := by
    cases hb : Nat.blt treeN (100 * c + j)
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) (by omega)
  rw [e1, e2, not_contains ht] at h
  simpa using h

theorem chunk_facts {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) (c : ℕ)
    (R : ℕ → NRec) (hall : ∀ j < 100, chunkNodeOK T c R j = true) (hedge : edgeChk c R = true)
    (hglob : c = 0 → globalOK = true) : burnsideJ4NP_TreeChunkFacts c := by
  refine ⟨fun k hk1 hk2 hk3 hkN hkt => ?_, fun k hk1 hkN hc hp => ?_, hglob⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = 100 * c + j := ⟨k - 100 * c, by omega⟩
    exact (node_sound hT hsx (chunkNode_sound (hall j (by omega)) hk3 hkN hkt)).1
  · unfold edgeChk at hedge
    have he := List.all_eq_true.mp hedge k (List.mem_range'_1.mpr ⟨hk1, by omega⟩)
    have e1 : (!((treeParent k).1 / 100 == c)) = false := by simp [hc]
    have e2 : ((treeParent k).1 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    rw [e1, e2] at he
    simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at he
    obtain ⟨⟨hpN, hpt⟩, htgt⟩ := he
    have hpt' : (treeParent k).1 ∉ treeTopIds := fun hm => by simp [hm] at hpt
    set p := (treeParent k).1 with hpdef
    have hp' : p = 100 * c + p % 100 := by omega
    have hpN' : p ≤ treeN := Nat.le_of_ble_eq_true hpN
    have hnode := hall (p % 100) (Nat.mod_lt _ (by norm_num))
    have hns0 := chunkNode_sound hnode (by omega) (by omega) (by rwa [← hp'])
    rw [← hp'] at hns0
    have hns := (node_sound hT hsx hns0).2
    set kd := (R (p % 100)).kids.getD (treeParent k).2 default
    have hk0 : kd.tgt ≠ 0 := by rw [htgt]; omega
    have hmem : kd ∈ (R (p % 100)).kids := by
      by_contra hn
      have hlen : ¬ (treeParent k).2 < (R (p % 100)).kids.length := fun hl =>
        hn (by simp only [kd]; rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _)
      have : kd = default := by
        simp only [kd]
        exact List.getD_eq_default _ _ (by omega)
      exact hk0 (by rw [this]; rfl)
    have := hns kd hmem hk0
    rwa [htgt] at this

theorem w_facts {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    (R : ℕ → WRec) (hall : ∀ k < 1328, wAllOK T R k = true) : burnsideJ4NP_WFacts := by
  intro k hk1 hkN
  have h := hall k (by have : treeN = 1327 := rfl; omega)
  unfold wAllOK at h
  have e1 : (k == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  have e2 : Nat.blt treeN k = false := by
    cases hb : Nat.blt treeN k
    · rfl
    · exact absurd (Nat.blt_eq.mp hb) (by omega)
  rw [e1, e2, Bool.false_or, Bool.false_or] at h
  exact w_sound hT hsx h

end Glue

end CFSG.KC.J4TreeN
