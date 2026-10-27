module

public import Certificates.Data.Kernel.RouteP.RigidTwin
public import Certificates.Data.RouteP.Rigid
public import CFSG.Certificates.Kernel.Spor.PK.NatBFS
public import CFSG.Certificates.Kernel.RouteP.TextLines
public import CFSG.Sporadic.Th.TableSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.RouteP

open CFSG.KS.PK CFSG.KC.RouteP CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native

theorem getD_mem' {l : List Nat} {k : Nat} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

theorem letters_congr {F G : Nat → Nat → Nat} {n h p : Nat} (hp : p < n) :
    ∀ (ls : List Nat), (∀ l ∈ ls, ∀ x < n, F l x < n) → (∀ l ∈ ls, ∀ x < n, F l x = G l x) →
      ∀ (s : BS), (∀ q ∈ s.pts, q < n) →
      ls.foldl (BS.letter F h p) s = ls.foldl (BS.letter G h p) s ∧
        ∀ q ∈ (ls.foldl (BS.letter F h p) s).pts, q < n
  | [], _, _, s, hs => ⟨rfl, hs⟩
  | l :: ls, hF, hFG, s, hs => by
    have e : BS.letter F h p s l = BS.letter G h p s l := by
      unfold BS.letter
      rw [hFG l List.mem_cons_self p hp]
    have hs' : ∀ q ∈ (BS.letter F h p s l).pts, q < n := by
      intro q hq
      unfold BS.letter at hq
      split at hq
      · exact hs q hq
      · simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hs q hq
        · exact hF l List.mem_cons_self p hp
    rw [List.foldl_cons, List.foldl_cons, ← e]
    exact letters_congr hp ls (fun l' hl' => hF l' (List.mem_cons_of_mem _ hl'))
      (fun l' hl' => hFG l' (List.mem_cons_of_mem _ hl')) _ hs'

theorem run_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n r : Nat} (hr : r < n)
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (hFG : ∀ l ∈ lv, ∀ x < n, F l x = G l x) :
    BS.run F lv n r = BS.run G lv n r := by
  have key : ∀ k, (List.range k).foldl (BS.step F lv) ⟨[r], [0], [0]⟩ =
      (List.range k).foldl (BS.step G lv) ⟨[r], [0], [0]⟩ ∧
      ∀ q ∈ ((List.range k).foldl (BS.step F lv) ⟨[r], [0], [0]⟩).pts, q < n := by
    intro k
    induction k with
    | zero => exact ⟨rfl, by simpa using hr⟩
    | succ k ih =>
      obtain ⟨e, hlt⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
        List.foldl_nil, List.foldl_nil, ← e]
      generalize (List.range k).foldl (BS.step F lv) ⟨[r], [0], [0]⟩ = s at hlt ⊢
      unfold BS.step
      by_cases hk : k < s.pts.length
      · rw [if_pos hk, if_pos hk]
        have hp : s.pts.getD k 0 < n := hlt _ (getD_mem' hk)
        exact letters_congr hp lv hF hFG s hlt
      · rw [if_neg hk, if_neg hk]
        exact ⟨rfl, hlt⟩
  unfold BS.run
  exact (key n).1

theorem ap_list_toArray {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ 32) (k : Nat) :
    ap (l.map UInt32.ofNat).toArray k = l.getD k 0 := by
  unfold ap
  by_cases hk : k < l.length
  · rw [getElem!_pos _ k (by simpa using hk)]
    simp only [List.getElem_toArray, List.getElem_map, UInt32.toNat_ofNat']
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact Nat.mod_eq_of_lt (hl _ (List.getElem_mem hk))
  · rw [getElem!_neg _ k (by simpa using hk)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

section Tree

variable {n : Nat} {F : Nat → Nat → Nat} {lv : List Nat} {r : Nat} {s : BS}

theorem treeOf_pts_ap (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) (k : Nat) :
    ap (treeOf n s).pts k = s.pts.getD k 0 :=
  ap_list_toArray (fun p hp => Nat.lt_trans (hs.lt p hp) hn) k

theorem treeOf_par_ap (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) (k : Nat) :
    ap (treeOf n s).par k = s.par.getD k 0 := by
  refine ap_list_toArray (fun x hx => ?_) k
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < s.pts.length := hs.len_par ▸ hi
  have hgd : s.par[i] = s.par.getD i 0 := List.getElem_eq_getD 0 (h := hi)
  rw [hgd]
  by_cases h0 : 0 < i
  · have := hs.par_lt i h0 hi'
    have := hs.le
    omega
  · have : i = 0 := by omega
    subst this
    rw [hs.par0]
    omega

theorem treeOf_lab_ap (hs : RunOK n F lv r s) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (k : Nat) :
    ap (treeOf n s).lab k = s.lab.getD k 0 := by
  refine ap_list_toArray (fun x hx => ?_) k
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < s.pts.length := hs.len_lab ▸ hi
  have hgd : s.lab[i] = s.lab.getD i 0 := List.getElem_eq_getD 0 (h := hi)
  rw [hgd]
  by_cases h0 : 0 < i
  · exact hlv _ (hs.lab_mem i h0 hi')
  · have : i = 0 := by omega
    subst this
    rw [hs.lab0]
    omega

theorem treeOf_pos_ap (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) {p : Nat} (hp : p < n)
    (hm : p ∈ s.pts) : ap (treeOf n s).pos p = s.pts.idxOf p := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_true, UInt32.toNat_ofNat']
  have := List.idxOf_lt_length_iff.mpr hm
  have := hs.le
  exact Nat.mod_eq_of_lt (by omega)

theorem treeOf_pos_nmem {p : Nat} (hp : p < n) (hm : p ∉ s.pts) :
    ap (treeOf n s).pos p = 2 ^ 32 - 1 := by
  unfold ap treeOf
  rw [getElem!_pos _ p (by simpa using hp)]
  simp only [Array.getElem_ofFn, hm, if_false]
  rfl

theorem treeOf_size : (treeOf n s).pts.size = s.pts.length := by
  simp [treeOf]


theorem getD_idxOf' {l : List Nat} {q : Nat} (hq : q ∈ l) : l.getD (l.idxOf q) 0 = q := by
  have hlt := List.idxOf_lt_length_of_mem hq
  rw [← List.getElem_eq_getD 0 (h := hlt)]
  exact List.getElem_idxOf hlt

theorem inTree_treeOf (hn : n < 2 ^ 32) (hs : RunOK n F lv r s) {v : Nat} (hv : v < n) :
    inTree (treeOf n s) v = s.pts.contains v := by
  unfold inTree
  by_cases hm : v ∈ s.pts
  · rw [treeOf_pos_ap hn hs hv hm, treeOf_size, treeOf_pts_ap hn hs, getD_idxOf' hm,
      List.contains_iff_mem.mpr hm]
    simp [List.idxOf_lt_length_of_mem hm]
  · rw [treeOf_pos_nmem hv hm, treeOf_size]
    have h1 : ¬ 2 ^ 32 - 1 < s.pts.length := by
      have := hs.le
      omega
    have h2 : s.pts.contains v = false := by simpa using hm
    simp only [h2, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.false_eq, beq_eq_false_iff_ne]
    left
    exact h1

theorem propLF_lt (hF : ∀ l, ∀ x < n, F l x < n) {c : Nat} (hc : c < n) :
    ∀ f k, propLF F s c f k < n
  | 0, _ => hc
  | f + 1, k => by
    unfold propLF
    split
    · exact hF _ _ (propLF_lt hF hc f _)
    · exact hc

theorem propLF_eq_of_le (c : Nat) : ∀ f g k, k ≤ f → k ≤ g → propLF F s c f k = propLF F s c g k
  | 0, g, k, hf, hg => by
    have : k = 0 := by omega
    subst this
    cases g <;> simp [propLF]
  | f + 1, 0, k, hf, hg => by
    have : k = 0 := by omega
    subst this
    simp [propLF]
  | f + 1, g + 1, k, hf, hg => by
    unfold propLF
    split
    · rename_i h
      rw [propLF_eq_of_le c f g _ (by omega) (by omega)]
    · rfl

theorem propL_eq (c k : Nat) : propL F s c k =
    if 0 < k ∧ s.par.getD k 0 < k then F (s.lab.getD k 0) (propL F s c (s.par.getD k 0)) else c := by
  unfold propL
  cases k with
  | zero => simp [propLF]
  | succ k =>
    have e : propLF F s c (k + 1) (k + 1) = if 0 < k + 1 ∧ s.par.getD (k + 1) 0 < k + 1 then
        F (s.lab.getD (k + 1) 0) (propLF F s c k (s.par.getD (k + 1) 0)) else c := rfl
    rw [e]
    split
    · rename_i h
      rw [propLF_eq_of_le c k _ _ (by omega) (Nat.le_refl _)]
    · rfl

theorem propagate_treeOf (hn : n < 2 ^ 32) (hs : RunOK n F lv r s)
    (hlv : ∀ l ∈ lv, l < 2 ^ 32) {L : Array Table}
    (hL : ∀ l ∈ lv, ∀ x < n, ap L[l]! x = F l x) (hF : ∀ l, ∀ x < n, F l x < n) (h0 : 0 ∈ lv)
    {c : Nat} (hc : c < n) : ∀ k, propagate (treeOf n s) L c k = propL F s c k := by
  intro k
  refine Nat.strongRecOn k ?_
  intro k ih
  rw [propagate, propL_eq, treeOf_par_ap hn hs, treeOf_lab_ap hs hlv]
  by_cases h : 0 < k ∧ s.par.getD k 0 < k
  · rw [dif_pos h, if_pos h, ih _ h.2]
    have hl : s.lab.getD k 0 ∈ lv := by
      rcases Nat.lt_or_ge k s.pts.length with hk | hk
      · exact hs.lab_mem k h.1 hk
      · have : s.lab.getD k 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hs.len_lab]; omega)]
          rfl
        rw [this]
        exact h0
    exact hL _ hl _ (propLF_lt hF hc _ _)
  · rw [dif_neg h, if_neg h]

theorem all_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem allIn_zero_eq' (m : Nat) (p : Nat → Bool) : allIn 0 m p = (List.range m).all p := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.Sporadic.Th.allIn_eq_true, List.all_eq_true]
  simp

theorem candOK_treeOf (hn : n < 2 ^ 32) {L : Array Table} (hs : RunOK n F (List.range L.size) r s)
    (hcl : ∀ p ∈ s.pts, ∀ l < L.size, F l p ∈ s.pts)
    (hL : ∀ l < L.size, ∀ x < n, ap L[l]! x = F l x) (hF : ∀ l, ∀ x < n, F l x < n)
    (hm : 0 < L.size) (hlv : L.size < 2 ^ 32) {c : Nat} (hc : c < n) :
    candOK L (treeOf n s) c = candTw F L.size s c := by
  have hlv' : ∀ l ∈ List.range L.size, l < 2 ^ 32 := fun l hl => by
    have := List.mem_range.1 hl
    omega
  have hL' : ∀ l ∈ List.range L.size, ∀ x < n, ap L[l]! x = F l x :=
    fun l hl => hL l (List.mem_range.1 hl)
  have hprop := propagate_treeOf hn hs hlv' hL' hF (List.mem_range.2 hm) hc
  unfold candOK candTw
  simp only [allIn_zero_eq']
  rw [treeOf_size]
  apply all_congr'
  intro k hk
  have hk := List.mem_range.1 hk
  apply all_congr'
  intro l hl
  have hl := List.mem_range.1 hl
  have hp := getD_mem' hk
  have hpn := hs.lt _ hp
  have hq := hcl _ hp l hl
  have hqn := hs.lt _ hq
  rw [treeOf_pts_ap hn hs, hL l hl _ hpn, treeOf_pos_ap hn hs hqn hq,
    getElem!_pos _ (s.pts.idxOf _) (by simpa [treeOf_size] using List.idxOf_lt_length_of_mem hq),
    Array.getElem_ofFn, getElem!_pos _ k (by simpa [treeOf_size] using hk),
    Array.getElem_ofFn, hprop, hprop]
  have e : ap L[l]! (propL F s c k) = F l (propL F s c k) := hL l hl _ (propLF_lt hF hc _ _)
  exact congrArg _ e

theorem toNat_map_ofNat {l : List Nat} (h : ∀ x ∈ l, x < 2 ^ 32) :
    (l.map UInt32.ofNat).map UInt32.toNat = l := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp, id, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (h x hx)

theorem candList_treeOf (hn : n < 2 ^ 32) {L : Array Table}
    (hs : RunOK n F (List.range L.size) r s) (hcl : ∀ p ∈ s.pts, ∀ l < L.size, F l p ∈ s.pts)
    (hL : ∀ l < L.size, ∀ x < n, ap L[l]! x = F l x) (hF : ∀ l, ∀ x < n, F l x < n)
    (hm : 0 < L.size) (hlv : L.size < 2 ^ 32) :
    candList L (treeOf n s) = s.pts.filter (candTw F L.size s) := by
  unfold candList
  have e : (treeOf n s).pts.toList.map UInt32.toNat = s.pts := by
    simp only [treeOf, List.toList_toArray]
    exact toNat_map_ofNat fun x hx => Nat.lt_trans (hs.lt x hx) hn
  rw [e]
  apply List.filter_congr
  intro c hc
  exact candOK_treeOf hn hs hcl hL hF hm hlv (hs.lt c hc)

theorem propL_root (hs : RunOK n F lv r s) : ∀ k < s.pts.length, propL F s r k = s.pts.getD k 0 := by
  intro k
  refine Nat.strongRecOn k ?_
  intro k ih hk
  rw [propL_eq]
  by_cases h0 : 0 < k
  · have hp := hs.par_lt k h0 hk
    rw [if_pos ⟨h0, hp⟩, ih _ hp (by omega), hs.edge k h0 hk]
  · have : k = 0 := by omega
    subst this
    rw [if_neg (by omega), hs.root]

theorem candTw_root {m : Nat} (hs : RunOK n F lv r s) (hcl : ∀ p ∈ s.pts, ∀ l < m, F l p ∈ s.pts) :
    candTw F m s r = true := by
  unfold candTw
  rw [List.all_eq_true]
  intro k hk
  rw [List.all_eq_true]
  intro l hl
  have hk' := List.mem_range.1 hk
  have hq := hcl _ (getD_mem' hk') l (List.mem_range.1 hl)
  rw [propL_root hs _ (List.idxOf_lt_length_of_mem hq), getD_idxOf' hq, propL_root hs _ hk']
  simp

end Tree

theorem foldl_congr'' {α β : Type} {f g : β → α → β} :
    ∀ {l : List α} {b : β}, (∀ x ∈ l, ∀ c, f c x = g c x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self]
    exact foldl_congr'' fun x hx c => h x (List.mem_cons_of_mem _ hx) c

theorem mark_spec : ∀ (ps : List Nat) (seen : Array Bool), (∀ p ∈ ps, p < seen.size) →
    (ps.foldl (fun b p => b.set! p true) seen).size = seen.size ∧
      ∀ x < seen.size, (ps.foldl (fun b p => b.set! p true) seen)[x]! = (seen[x]! || ps.contains x)
  | [], seen, _ => ⟨rfl, fun x _ => by simp⟩
  | p :: ps, seen, h => by
    have hp := h p List.mem_cons_self
    have hsz : (seen.set! p true).size = seen.size := by simp
    obtain ⟨h1, h2⟩ := mark_spec ps (seen.set! p true) (fun q hq => by
      rw [hsz]
      exact h q (List.mem_cons_of_mem _ hq))
    rw [List.foldl_cons]
    refine ⟨h1.trans hsz, fun x hx => ?_⟩
    rw [h2 x (by rw [hsz]; exact hx)]
    rw [getElem!_pos _ x (by rw [hsz]; exact hx), getElem!_pos _ x hx]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, List.contains_cons]
    by_cases e : p = x
    · subst e
      simp
    · rw [Array.getElem_setIfInBounds_ne hx e]
      have : (x == p) = false := by simpa using Ne.symm e
      simp [this]

theorem orbitTrees_eq {n : Nat} (hn : n < 2 ^ 32) {L : Array Table} {F : Nat → Nat → Nat}
    (hL : ∀ l < L.size, ∀ x < n, ap L[l]! x = F l x) (hF : ∀ l, ∀ x < n, F l x < n) :
    orbitTrees n L = (orbitBS F L.size n).map (treeOf n) := by
  have hF' : ∀ l ∈ (Array.range L.size).toList, ∀ x < n, tabF L l x < n := by
    intro l hl x hx
    have hl' : l < L.size := by simpa using hl
    unfold tabF
    rw [hL l hl' x hx]
    exact hF l x hx
  have hrun : ∀ r < n, treeBFS n r L (Array.range L.size) =
      treeOf n (BS.run F (List.range L.size) n r) := by
    intro r hr
    rw [treeBFS_eq (by omega) hr hF', Array.toList_range]
    congr 1
    apply run_congr hr
    · intro l hl x hx
      have hl' := List.mem_range.1 hl
      unfold tabF
      rw [hL l hl' x hx]
      exact hF l x hx
    · intro l hl x hx
      exact hL l (List.mem_range.1 hl) x hx
  have hFl : ∀ l ∈ List.range L.size, ∀ x < n, F l x < n := fun l _ x hx => hF l x hx
  let g : Array Bool × Array Tree → Nat → Array Bool × Array Tree := fun st r =>
    if (!st.1[r]!) = true then
      ((treeBFS n r L (Array.range L.size)).pts.foldl (fun b a => b.set! a.toNat true) st.1,
        st.2.push (treeBFS n r L (Array.range L.size)))
    else (st.1, st.2)
  let gB : List Nat × List BS → Nat → List Nat × List BS := fun st r =>
    if st.1.contains r then st else
      (st.1 ++ (BS.run F (List.range L.size) n r).pts, st.2 ++ [BS.run F (List.range L.size) n r])
  let Rel : Array Bool × Array Tree → List Nat × List BS → Prop := fun A B =>
    A.1.size = n ∧ (∀ x < n, A.1[x]! = B.1.contains x) ∧ A.2.toList = B.2.map (treeOf n) ∧
      ∀ x ∈ B.1, x < n
  have step : ∀ r < n, ∀ A B, Rel A B → Rel (g A r) (gB B r) := by
    intro r hr A B hAB
    obtain ⟨h1, h2, h3, h4⟩ := hAB
    by_cases hc : B.1.contains r = true
    · have hg : g A r = (A.1, A.2) := by
        simp only [g, h2 r hr, hc, Bool.not_true, Bool.false_eq_true, if_false]
      have hgB : gB B r = B := by simp only [gB, hc, if_true]
      rw [hg, hgB]
      exact ⟨h1, h2, h3, h4⟩
    · have hc' : B.1.contains r = false := by simpa using hc
      have hok := run_ok hFl hr
      set_option linter.unusedVariables false in
      have hg : g A r = ((BS.run F (List.range L.size) n r).pts.foldl (fun b p => b.set! p true) A.1,
          A.2.push (treeOf n (BS.run F (List.range L.size) n r))) := by
        simp only [g, h2 r hr, hc', Bool.not_false, if_true, hrun r hr]
        congr 1
        simp only [treeOf, List.foldl_toArray, List.foldl_map]
        apply foldl_congr''
        intro x hx b
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := hok.lt x hx; omega)]
      have hgB : gB B r = (B.1 ++ (BS.run F (List.range L.size) n r).pts,
          B.2 ++ [BS.run F (List.range L.size) n r]) := by simp only [gB, hc', Bool.false_eq_true, if_false]
      rw [hg, hgB]
      obtain ⟨m1, m2⟩ := mark_spec (BS.run F (List.range L.size) n r).pts A.1
        (fun p hp => by rw [h1]; exact hok.lt p hp)
      refine ⟨m1.trans h1, fun x hx => ?_, ?_, ?_⟩
      · rw [m2 x (by rw [h1]; exact hx), h2 x hx, List.contains_append]
      · simp [h3]
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h4 x hx
        · exact hok.lt x hx
  have sim : ∀ (rs : List Nat), (∀ r ∈ rs, r < n) → ∀ A B, Rel A B →
      Rel (rs.foldl g A) (rs.foldl gB B) := by
    intro rs
    induction rs with
    | nil => intro _ A B h; exact h
    | cons r rs ih =>
      intro hrs A B h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) _ _
        (step r (hrs r List.mem_cons_self) A B h)
  have h0 : Rel (Array.replicate n false, #[]) (([] : List Nat), ([] : List BS)) := by
    refine ⟨by simp, fun x hx => ?_, rfl, fun x hx => by simp at hx⟩
    rw [getElem!_pos _ x (by simpa using hx)]
    simp
  have hfin := (sim (List.range' 0 n) (fun r hr => by simp at hr; omega) _ _ h0).2.2.1
  unfold orbitTrees
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Array.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  rw [forIn_yield_foldl _ _ g (by intro a b; simp only [g]; split <;> rfl)]
  have e : (n - 0 + 1 - 1) / 1 = n := by omega
  rw [e]
  unfold orbitBS
  simp only [gB, g, List.range_eq_range'] at hfin ⊢
  exact hfin

theorem combined_treeOf {n : Nat} (hn : n < 2 ^ 32) {L : Array Table} {F : Nat → Nat → Nat}
    (hL : ∀ l < L.size, ∀ x < n, ap L[l]! x = F l x) (hF : ∀ l, ∀ x < n, F l x < n)
    (hm : 0 < L.size) (hlv : L.size < 2 ^ 32) {v : Nat} (hv : v < n) :
    ∀ (ss : List BS) (cs : List Nat), (∀ s ∈ ss, ∃ r, RunOK n F (List.range L.size) r s) →
      (∀ c ∈ cs, c < n) → combined L (ss.map (treeOf n)) cs v = combinedTw F ss cs v
  | [], _, _, _ => by cases ‹List Nat› <;> rfl
  | _ :: _, [], _, _ => rfl
  | s :: ss, c :: cs, hss, hcs => by
    obtain ⟨r, hs⟩ := hss s List.mem_cons_self
    have hlv' : ∀ l ∈ List.range L.size, l < 2 ^ 32 := fun l hl => by
      have := List.mem_range.1 hl
      omega
    have hL' : ∀ l ∈ List.range L.size, ∀ x < n, ap L[l]! x = F l x :=
      fun l hl => hL l (List.mem_range.1 hl)
    rw [List.map_cons]
    unfold combined combinedTw
    rw [inTree_treeOf hn hs hv]
    split
    · rename_i hm'
      have hmem : v ∈ s.pts := by simpa using hm'
      rw [treeOf_pos_ap hn hs hv hmem,
        propagate_treeOf hn hs hlv' hL' hF (List.mem_range.2 hm) (hcs c List.mem_cons_self)]
    · exact combined_treeOf hn hL hF hm hlv hv ss cs (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs'))
        (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))

end CFSG.KS.RouteP
