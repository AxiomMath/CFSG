
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Native
public import CFSG.Sporadic.J4.QT2ASyl
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QT2LocX0MainBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

@[expose] public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 Matrix

section Cert

variable (ws : List (List ℤ))

noncomputable def gEl (k : ℕ) : J := QT2A.el5 (ws.getD k [])

noncomputable def eEl (m : ℕ) : J := QT2A.el5 (eW ws m)

noncomputable def Vgrp : Subgroup J :=
  Subgroup.closure {x | x ∈ ws.map QT2A.el5}

variable {ws}

theorem eTab_size : (eTab ws).size = 16 := by simp [eTab]

theorem eTab_get {m : ℕ} (hm : m < 16) : (eTab ws)[m]! = wR (eW ws m) := by
  rw [getElem!_pos (eTab ws) m (by rw [eTab_size]; exact hm)]
  simp [eTab]

theorem mem_eList {e : Array V2} : e ∈ eList ws ↔ ∃ m < 16, e = eR ws m := by
  unfold eList
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, h.symm⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, h.symm⟩

theorem el5_nil : QT2A.el5 [] = 1 := by simp [QT2A.el5, wordProd]

theorem el5_append (w w' : List ℤ) : QT2A.el5 (w ++ w') = QT2A.el5 w * QT2A.el5 w' :=
  QT2A.wordProd_append QT2A.gen5 w w'

theorem el5_flatMap_mem {Q : Subgroup J} (l : List ℕ) (f : ℕ → List ℤ)
    (h : ∀ i ∈ l, QT2A.el5 (f i) ∈ Q) : QT2A.el5 (l.flatMap f) ∈ Q := by
  induction l with
  | nil => simp [el5_nil]
  | cons i l ih =>
    rw [List.flatMap_cons, el5_append]
    exact Q.mul_mem (h i (List.mem_cons_self ..))
      (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem xor_lt_sixteen {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 := by
  have h := Nat.xor_lt_two_pow (n := 4) (x := a) (y := b) (by simpa using ha) (by simpa using hb)
  simpa using h

theorem chkGrp_parts (h : chkGrp ws = true) :
    ws.length = 4 ∧ (∀ m < 16, wfR (eR ws m) = true) ∧ eqRows (eR ws 0) idRows = true ∧
    allDistinct ((List.range 16).map (eR ws)) = true ∧
    (∀ m < 16, ∀ m' < 16, eqRows (mulRows (eR ws m) (eR ws m')) (eR ws (m ^^^ m')) = true) ∧
    (∀ k < 4, eqRows (wR (ws.getD k [])) (eR ws (2 ^ k)) = true) := by
  unfold chkGrp at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem gEl_mem (hg : chkGrp ws = true) {k : ℕ} (hk : k < 4) : gEl ws k ∈ Vgrp ws := by
  obtain ⟨hlen, -⟩ := chkGrp_parts hg
  apply Subgroup.subset_closure
  refine List.mem_map.2 ⟨ws.getD k [], ?_, rfl⟩
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem eEl_mem (hg : chkGrp ws = true) (m : ℕ) : eEl ws m ∈ Vgrp ws := by
  unfold eEl eW
  refine el5_flatMap_mem _ _ fun k hk => ?_
  have hk4 : k < 4 := List.mem_range.1 hk
  by_cases hb : m.testBit k
  · rw [ite_eq_left hb]
    exact gEl_mem hg hk4
  · rw [ite_eq_right hb, el5_nil]
    exact Subgroup.one_mem _

theorem chkNorm_parts (h : chkNorm ws = true) :
    (∀ m < 16, ∃ m' < 16,
      eqRows (mulRows xR (eR ws m)) (mulRows (eR ws m') xR) = true) ∧
    ∀ m < 15, eqRows (mulRows xR (eR ws (m + 1))) (mulRows (eR ws (m + 1)) xR) = false := by
  unfold chkNorm at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun m hm => by
    obtain ⟨m', hm', he⟩ := h1 m hm
    exact ⟨m', hm', he⟩, h2⟩

theorem ordRows_of_orderOf {g : J} {M : Array V2} (hg : Mx g = rowsMatrix M)
    (hM : wfR M = true) {r : ℕ} (hr : orderOf g = r) (hr1 : r ≠ 1) : ordRows M r = true := by
  unfold ordRows
  rw [Bool.and_eq_true]
  constructor
  · rw [Bool.not_eq_true']
    by_contra hc
    have hc' : eqRows M idRows = true := by simpa using hc
    have h1 := eqRows_iff.1 hc'
    have e : g = 1 := by
      apply Mx_injective
      rw [hg, h1, rowsMatrix_idRows, map_one]
    apply hr1
    rw [← hr, e, orderOf_one]
  · apply eqRows_iff.2
    apply eq_of_rowsMatrix_eq (wfR_powRows hM r) wfR_idRows
    rw [rowsMatrix_powRows, ← hg, ← map_pow, ← hr, pow_orderOf_eq_one, map_one,
      rowsMatrix_idRows]

theorem chkK0_spec (h : chkK0 ws = true) {q : ℕ} (hq : q < 6720)
    (hcomm : ∀ k < 4, eqRows (mulRows x0Orb.mats[q]! (wR (ws.getD k [])))
      (mulRows (wR (ws.getD k [])) x0Orb.mats[q]!) = true) :
    ordRows x0Orb.mats[q]! 3 = false ∧ ordRows x0Orb.mats[q]! 7 = false ∧
      ordRows x0Orb.mats[q]! 23 = false := by
  unfold chkK0 at h
  dsimp only at h
  have h1 := List.all_eq_true.1 h q (List.mem_range.2 hq)
  have h2 : (List.map (fun k => wR (ws.getD k [])) (List.range 4)).all
      (fun g => eqRows (mulRows x0Orb.mats[q]! g) (mulRows g x0Orb.mats[q]!)) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    exact hcomm k (List.mem_range.1 hk)
  simp only [h2, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨⟨a, b⟩, c⟩ := h1
  exact ⟨a, b, c⟩

end Cert

end CFSG.QuasithinUnique.A5.Dec2
