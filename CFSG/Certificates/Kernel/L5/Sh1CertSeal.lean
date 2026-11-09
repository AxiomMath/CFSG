module

public import CFSG.Certificates.Kernel.L5.Fast

public section

namespace CFSG.Certificates.Kernel.L5Seal

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] noncomputable def wordC (gs : List (CV 16)) (w : List ℕ) : CV 16 :=
  w.foldl (fun acc i => acc * gs.getD i 1) 1

theorem mem_cl_succ {gs : List (CV 16)} {k : ℕ} {x : CV 16} (hx : x ∈ closureList gs k) :
    x ∈ closureList gs (k + 1) := by
  simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
    List.mem_append]
  exact Or.inl hx

theorem mem_cl_mul {gs : List (CV 16)} {k : ℕ} {x g : CV 16} (hx : x ∈ closureList gs k)
    (hg : g ∈ gs) : x * g ∈ closureList gs (k + 1) := by
  simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
    List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨x, hx, g, hg, rfl⟩

theorem mem_cl_le {gs : List (CV 16)} {x : CV 16} {k m : ℕ} (h : k ≤ m)
    (hx : x ∈ closureList gs k) : x ∈ closureList gs m := by
  induction m, h using Nat.le_induction with
  | base => exact hx
  | succ m _ ih => exact mem_cl_succ ih

theorem one_mem_cl (gs : List (CV 16)) : (1 : CV 16) ∈ closureList gs 0 :=
  List.mem_singleton_self _

theorem getD_mem_or (gs : List (CV 16)) (i : ℕ) : gs.getD i 1 ∈ gs ∨ gs.getD i 1 = 1 := by
  rcases Nat.lt_or_ge i gs.length with h | h
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ h

theorem foldl_mem_cl (gs : List (CV 16)) : ∀ (w : List ℕ) (acc : CV 16) (k : ℕ),
    acc ∈ closureList gs k →
      w.foldl (fun acc i => acc * gs.getD i 1) acc ∈ closureList gs (k + w.length)
  | [], acc, k, h => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact h
  | i :: w, acc, k, h => by
    rw [List.foldl_cons, List.length_cons, show k + (w.length + 1) = k + 1 + w.length by omega]
    refine foldl_mem_cl gs w _ (k + 1) ?_
    show acc * gs.getD i 1 ∈ closureList gs (k + 1)
    rcases getD_mem_or gs i with hg | hg
    · exact mem_cl_mul h hg
    · rw [hg, mul_one]
      exact mem_cl_succ h

theorem wordC_mem (gs : List (CV 16)) (w : List ℕ) {k : ℕ} (hw : w.length ≤ k) :
    wordC gs w ∈ closureList gs k := by
  have h := foldl_mem_cl gs w 1 0 (one_mem_cl gs)
  rw [Nat.zero_add] at h
  exact mem_cl_le hw h

theorem cl_sub (gs T : List (CV 16)) (h1 : (1 : CV 16) ∈ T)
    (hT : ∀ x ∈ T, ∀ g ∈ gs, x * g ∈ T) : ∀ k, ∀ y ∈ closureList gs k, y ∈ T
  | 0, y, hy => by
    have hy' : y ∈ [(1 : CV 16)] := hy
    rw [List.mem_singleton] at hy'
    rw [hy']
    exact h1
  | k + 1, y, hy => by
    simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
      List.mem_append, List.mem_flatMap, List.mem_map] at hy
    rcases hy with hy | ⟨x, hx, g, hg, rfl⟩
    · exact cl_sub gs T h1 hT k y hy
    · exact hT x (cl_sub gs T h1 hT k x hx) g hg

theorem cl_nodup (gs : List (CV 16)) (k : ℕ) : (closureList gs (k + 1)).Nodup := by
  simp only [closureList, Function.iterate_succ_apply', closureStep]
  exact List.nodup_dedup _

theorem cl_perm_of (gs : List (CV 16)) (W : List (List ℕ)) (k : ℕ)
    (hT : (W.map (wordC gs)).Nodup) (h1 : (1 : CV 16) ∈ W.map (wordC gs))
    (hc : ∀ x ∈ W.map (wordC gs), ∀ g ∈ gs, x * g ∈ W.map (wordC gs))
    (hl : ∀ w ∈ W, w.length ≤ k + 1) :
    (closureList gs (k + 1)).Perm (W.map (wordC gs)) :=
  (List.perm_ext_iff_of_nodup (cl_nodup gs k) hT).2 fun x =>
    ⟨fun hx => cl_sub gs _ h1 hc (k + 1) x hx, fun hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact wordC_mem gs w (hl w hw)⟩

theorem all_perm {α : Type*} {l l' : List α} (h : l.Perm l') (p : α → Bool) :
    l.all p = l'.all p := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

theorem mulClosed_perm {l l' : List (CV 16)} (h : l.Perm l') :
    mulClosedChkP l = mulClosedChkP l' := by
  rw [Bool.eq_iff_iff]
  unfold mulClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq, h.mem_iff]

theorem invClosed_perm {l l' : List (CV 16)} (h : l.Perm l') :
    invClosedChkP l = invClosedChkP l' := by
  rw [Bool.eq_iff_iff]
  unfold invClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq, h.mem_iff]

@[expose] def sh1Words : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4], [5], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [1, 2], [1, 3],
    [1, 4], [1, 5], [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [4, 1], [4, 3], [4, 5], [5, 0],
    [5, 1], [5, 4], [0, 1, 2], [0, 1, 3], [0, 1, 5], [0, 2, 3], [0, 2, 4], [0, 2, 5], [0, 3, 4],
    [0, 4, 3], [0, 4, 5], [0, 5, 1], [0, 5, 4], [1, 2, 3], [1, 2, 4], [1, 3, 4], [1, 3, 5],
    [1, 4, 3], [1, 4, 5], [1, 5, 0], [1, 5, 4], [2, 3, 5], [2, 4, 1], [2, 4, 5], [2, 5, 0],
    [2, 5, 4], [3, 4, 1], [3, 4, 5], [3, 5, 1], [3, 5, 4], [4, 1, 3], [4, 1, 5], [4, 3, 5],
    [4, 5, 0], [4, 5, 1], [4, 5, 4], [5, 0, 1], [5, 0, 4], [5, 1, 4], [5, 4, 1], [5, 4, 3],
    [5, 4, 5], [0, 1, 2, 3], [0, 1, 5, 4], [0, 2, 4, 5], [0, 2, 5, 4], [0, 3, 4, 5],
    [0, 4, 5, 1], [0, 4, 5, 4], [0, 5, 1, 4], [0, 5, 4, 1], [0, 5, 4, 3], [0, 5, 4, 5],
    [1, 3, 4, 5], [1, 3, 5, 4], [1, 4, 3, 5], [1, 4, 5, 0], [1, 4, 5, 4], [1, 5, 0, 4],
    [1, 5, 4, 5], [2, 4, 5, 4], [2, 5, 4, 5], [3, 4, 1, 5], [3, 4, 5, 4], [3, 5, 4, 5],
    [4, 1, 5, 4], [4, 3, 5, 4], [4, 5, 0, 4], [4, 5, 1, 4], [4, 5, 4, 1], [4, 5, 4, 5],
    [5, 0, 4, 5], [5, 1, 4, 5], [5, 4, 1, 5], [5, 4, 3, 5], [5, 4, 5, 0], [5, 4, 5, 1],
    [0, 1, 5, 4, 5], [0, 2, 4, 5, 4], [0, 3, 4, 5, 4], [0, 4, 5, 1, 4], [0, 4, 5, 4, 1],
    [0, 4, 5, 4, 5], [0, 5, 1, 4, 5], [0, 5, 4, 1, 5], [0, 5, 4, 3, 5], [0, 5, 4, 5, 1],
    [1, 4, 3, 5, 4], [1, 4, 5, 0, 4], [1, 4, 5, 4, 5], [2, 4, 5, 4, 5], [3, 4, 5, 4, 5],
    [4, 1, 5, 4, 5], [4, 3, 5, 4, 5], [4, 5, 0, 4, 5], [4, 5, 1, 4, 5], [4, 5, 4, 1, 5],
    [4, 5, 4, 5, 0], [4, 5, 4, 5, 1], [5, 0, 4, 5, 4], [5, 1, 4, 5, 4], [5, 4, 1, 5, 4],
    [5, 4, 5, 1, 4]]

@[expose] noncomputable def sh1T : List (CV 16) := sh1Words.map (wordC (sh1Gens.map cOf))

set_option maxRecDepth 100000 in
theorem sh1T_base : (decide sh1T.Nodup && (decide ((1 : CV 16) ∈ sh1T) &&
    ((sh1T.all fun x => (sh1Gens.map cOf).all fun g => decide (x * g ∈ sh1T)) &&
      sh1Words.all fun w => decide (w.length ≤ 12)))) = true := by
  decide +kernel

theorem sh1T_closed : ∀ x ∈ sh1T, ∀ g ∈ sh1Gens.map cOf, x * g ∈ sh1T := by
  have h := sh1T_base
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2.2.1

theorem sh1C_perm : (closureList (sh1Gens.map cOf) 12).Perm sh1T := by
  have h := sh1T_base
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact cl_perm_of _ sh1Words 11 h.1 h.2.1 h.2.2.1 h.2.2.2

theorem sh1L_perm : Sh1L.Perm (sh1T.map ev) := by
  have e : Sh1L = (closureList (sh1Gens.map cOf) 12).map ev := by
    rw [← closureList_map_ev, map_cOf_ev]
    rfl
  rw [e]
  exact sh1C_perm.map ev

end CFSG.Certificates.Kernel.L5Seal

end
