
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public import Mathlib.Data.List.GetD

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.KT

open Equiv Perm CFSG.GH74.GLS.C3.Layer2.L5

theorem length_flatMap_range {β : Type*} (m n : ℕ) (g : ℕ → ℕ → β) :
    ((List.range m).flatMap fun a => (List.range n).map (g a)).length = m * n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [Nat.succ_mul]

theorem getD_flatMap_range {β : Type*} (m n : ℕ) (g : ℕ → ℕ → β) (d : β) {a b : ℕ}
    (ha : a < m) (hb : b < n) :
    ((List.range m).flatMap fun a => (List.range n).map (g a)).getD (a * n + b) d = g a b := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : a < m
    · have hlt : a * n + b < m * n := by
        have : (a + 1) * n ≤ m * n := Nat.mul_le_mul_right n h
        rw [Nat.succ_mul] at this
        omega
      rw [List.getD_append _ _ _ _ (by rw [length_flatMap_range]; exact hlt), ih h]
    · have e : a = m := by omega
      subst e
      rw [List.getD_append_right _ _ _ _ (by rw [length_flatMap_range]; omega),
        length_flatMap_range, Nat.add_sub_cancel_left]
      simp [List.getD_eq_getElem?_getD, hb]

theorem getD_toArray {β : Type*} (l : List β) (i : ℕ) (d : β) : l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem mt0_getD {a b : ℕ} (ha : a < 128) (hb : b < 128) :
    mt0.getD (a * 128 + b) 0 = sh0Idx (Sh0L.getD a 1 * Sh0L.getD b 1) := by
  unfold mt0
  simp only [getD_toArray]
  exact getD_flatMap_range 128 128 _ 0 ha hb

theorem inv0_getD {a : ℕ} (ha : a < Sh0L.length) : inv0.getD a 0 = sh0Idx (Sh0L.getD a 1)⁻¹ := by
  unfold inv0
  rw [getD_toArray, List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map,
    List.getD_eq_getElem _ _ ha]

theorem sh0Idx_getElem (hn : (Sh0L.map pcode).Nodup) {k : ℕ} (hk : k < Sh0L.length) :
    sh0Idx Sh0L[k] = k := by
  unfold sh0Idx sh0Codes
  have e : pcode Sh0L[k] = (Sh0L.map pcode)[k]'(by simpa using hk) := by simp
  rw [e, List.Nodup.idxOf_getElem hn]

theorem mt0Chk_of (hn : (Sh0L.map pcode).Nodup) (hc : mulClosedChkP Sh0L = true)
    (hl : Sh0L.length = 128) : mt0Chk = true := by
  unfold mt0Chk
  unfold mulClosedChkP at hc
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
  intro a ha b hb
  have ha' : a < Sh0L.length := by omega
  have hb' : b < Sh0L.length := by omega
  rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at *
  have hm := hc _ (List.getElem_mem ha') _ (List.getElem_mem hb')
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hm
  rw [mt0_getD ha hb, List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb', ← e,
    sh0Idx_getElem hn hk, List.getD_eq_getElem _ _ hk]
  exact ⟨by omega, rfl⟩

theorem inv0Chk_of (hn : (Sh0L.map pcode).Nodup) (hc : invClosedChkP Sh0L = true)
    (hl : Sh0L.length = 128) : inv0Chk = true := by
  unfold inv0Chk
  unfold invClosedChkP at hc
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
  intro a ha
  have ha' : a < Sh0L.length := by omega
  have hm := hc _ (List.getElem_mem ha')
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hm
  rw [inv0_getD ha', List.getD_eq_getElem _ _ ha', ← e, sh0Idx_getElem hn hk,
    List.getD_eq_getElem _ _ hk]
  exact ⟨by omega, rfl⟩

end CFSG.GH74.GLS.C3.Layer2.L5.KT

end
