
module

public import Certificates.Data.Kernel.L5.Sh0T
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.L5.Tables
public import CFSG.GH74.GLS.C3.Layer2.L5C5dInputs
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Certificates.Kernel.L5S

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

theorem sh0L_eq : Sh0L = sh0C.map ev := by
  simp only [Sh0L, sh0C, d8C, List.map_flatMap, List.map_map, Function.comp_def, ev_mul, ev_cOf]

theorem sh0L_getD (a : Nat) : Sh0L.getD a 1 = ev (sh0C.getD a 1) := by
  rw [sh0L_eq, ← ev_one, List.getD_map]

theorem sh0L_length : Sh0L.length = 128 := by
  rw [sh0L_eq, List.length_map]
  decide +kernel

theorem getD_toList {α : Type*} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = a.toList.getD i d := by
  rw [← KT.getD_toArray, Array.toArray_toList]

section

variable (hc : sh0Chk = true) (hn : ((sh0C.map ev).map pcode).Nodup)
include hc hn

theorem sh0_codes : (Sh0L.map pcode).Nodup := by rw [sh0L_eq]; exact hn

theorem mF_spec {a b : Nat} (ha : a < 128) (hb : b < 128) :
    mF a b < 128 ∧ Sh0L.getD a 1 * Sh0L.getD b 1 = Sh0L.getD (mF a b) 1 := by
  unfold sh0Chk at hc
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, h⟩ := hc a ha
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨h1, ?_⟩
  rw [sh0L_getD, sh0L_getD, sh0L_getD, ← ev_mul, h2]

theorem iF_spec {a : Nat} (ha : a < 128) :
    iF a < 128 ∧ (Sh0L.getD a 1)⁻¹ = Sh0L.getD (iF a) 1 := by
  unfold sh0Chk at hc
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, -⟩ := hc a ha
  refine ⟨h1, ?_⟩
  rw [sh0L_getD, sh0L_getD, ← ev_inv, h2]

theorem sh0Idx_getD {k : Nat} (hk : k < 128) : sh0Idx (Sh0L.getD k 1) = k := by
  have hk' : k < Sh0L.length := by rw [sh0L_length]; exact hk
  rw [List.getD_eq_getElem _ _ hk', KT.sh0Idx_getElem (sh0_codes hc hn) hk']

theorem mt0_getD_eq (n : Nat) : mt0.getD n 0 = tF n := by
  unfold tF
  split_ifs with h
  · have ha : n / 128 < 128 := by omega
    have hb : n % 128 < 128 := Nat.mod_lt _ (by norm_num)
    obtain ⟨h1, h2⟩ := mF_spec hc hn ha hb
    have e : n = n / 128 * 128 + n % 128 := by omega
    conv_lhs => rw [e]
    rw [KT.mt0_getD ha hb, h2, sh0Idx_getD hc hn h1]
  · unfold mt0
    simp only [KT.getD_toArray]
    rw [List.getD_eq_default _ _ (by rw [KT.length_flatMap_range]; omega)]

theorem inv0_getD_eq (n : Nat) : inv0.getD n 0 = iT n := by
  unfold iT
  split_ifs with h
  · obtain ⟨h1, h2⟩ := iF_spec hc hn h
    rw [KT.inv0_getD (by rw [sh0L_length]; exact h), h2, sh0Idx_getD hc hn h1]
  · unfold inv0
    rw [KT.getD_toArray, List.getD_eq_default _ _ (by rw [List.length_map, sh0L_length]; omega)]

theorem mt0_fun : (fun n => mt0.getD n 0) = tF := funext (mt0_getD_eq hc hn)

theorem inv0_fun : (fun n => inv0.getD n 0) = iT := funext (inv0_getD_eq hc hn)

end

theorem bfsWordsGo_eq (gs : List Nat) (fuel : Nat) (W : Array (Option (List Nat)))
    (fr : List Nat) : bfsWordsGo gs fuel W fr = bfsWordsGoT (fun n => mt0.getD n 0) gs fuel W fr := by
  induction fuel generalizing W fr with
  | zero => rfl
  | succ fuel ih =>
    rw [bfsWordsGo, bfsWordsGoT, ih]
    rfl

theorem Wd_eq : Wd = WdT (fun n => mt0.getD n 0) gI := by
  unfold Wd WdT
  rw [bfsWordsGo_eq]

theorem relsL_perm :
    relsL.Perm (relsUT (fun n => mt0.getD n 0) gI fun i => Wd.getD i []) := by
  unfold relsL
  exact List.mergeSort_perm _ _

theorem all_eq_of_perm {α : Type*} {l l' : List α} (h : l.Perm l') (P : α → Bool) :
    l.all P = l'.all P := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

theorem all_cons_of_mem {α : Type*} {r : α} {l : List α} (h : r ∈ l) (P : α → Bool) :
    l.all P = (r :: l).all P := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine ⟨fun H x hx => ?_, fun H x hx => H x (List.mem_cons_of_mem _ hx)⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · exact H x h
  · exact H x hx

theorem classifyChk_eq_T : classifyChk = classifyT (fun n => mt0.getD n 0) (fun n => inv0.getD n 0)
    gI (fun i => Wd.getD i []) relsL RIdx invL zc xsData ssData := by
  unfold classifyChk autPairOK twistOK classifyT classifyRowT autPairOKT twistOKT evI evFrom evFromT
    conjI conjIT
  rfl

theorem classifyT_congr_rels (t iv : Nat → Nat) (gs : List Nat) (W : Nat → List Nat)
    {R R' : List (List Nat × List Nat)} (h : ∀ P, R.all P = R'.all P) (ridx invl : List Nat)
    (z : Nat) (xs : List (List Nat)) (ss : List Nat) :
    classifyT t iv gs W R ridx invl z xs ss = classifyT t iv gs W R' ridx invl z xs ss := by
  unfold classifyT classifyRowT
  simp only [h]

theorem invL_eq : invL = invLT (fun n => mt0.getD n 0) := by
  unfold invL invLT
  rfl

theorem RIdx_eq : RIdx = RIdxC := by
  unfold RIdx RIdxC
  congr 1
  funext i
  have e : RhatL0 = ((List.finRange 16).map fun v => cOf (tr16 v)).map ev := by
    simp only [RhatL0, List.map_map, Function.comp_def, ev_cOf]
  rw [sh0L_getD, e, decide_mem_map_ev]

section

variable (hc : sh0Chk = true) (hn : ((sh0C.map ev).map pcode).Nodup)
include hc hn

theorem Wd_getD_eq (i : Nat) : Wd.getD i [] = wdK.getD i [] := by
  rw [getD_toList, Wd_eq, mt0_fun hc hn]
  rfl

theorem W_fun : (fun i => Wd.getD i []) = fun i => wdK.getD i [] := funext (Wd_getD_eq hc hn)

theorem relsL_all (hm : relK ∈ relsK) (P : List Nat × List Nat → Bool) :
    relsL.all P = (relK :: relsK).all P := by
  rw [all_eq_of_perm relsL_perm, mt0_fun hc hn, W_fun hc hn, ← all_cons_of_mem hm]
  rfl

theorem classifyChk_eq (hm : relK ∈ relsK) : classifyChk =
    classifyT tF iT gsK (fun i => wdK.getD i []) (relK :: relsK) RIdxC (invLT tF) 32 xsK ssK := by
  rw [classifyChk_eq_T, classifyT_congr_rels _ _ _ _ (relsL_all hc hn hm), invL_eq, RIdx_eq,
    mt0_fun hc hn, inv0_fun hc hn, W_fun hc hn]
  rfl

theorem classifyChk_of (hm : relK ∈ relsK) (hl : (invLT tF).all (fun x => decide (x < 128)) = true)
    (hk : ∀ c < 12, classifyK c = true) : classifyChk = true := by
  rw [classifyChk_eq hc hn hm]
  unfold classifyT
  rw [List.all_eq_true]
  intro x hx
  have hx' : x < 128 := of_decide_eq_true (List.all_eq_true.1 hl x hx)
  have h0 := hk (x / 11) (by omega)
  unfold classifyK at h0
  rw [List.all_eq_true] at h0
  have h := h0 x hx
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at h
  exact h

theorem genChk_eq : genChk = (((List.range 3).all fun k =>
    decide (tF (gsK.getD k 0 * 128 + gsK.getD k 0) = 0)) && decide (32 ≠ 0) && decide (32 < 128)) := by
  unfold genChk
  simp only [mt0_getD_eq hc hn]
  rfl

theorem gamTabs_getD {m j : Nat} (hm : m < 4) (hj : j < 128) :
    (gamTabs.getD m #[]).getD j 0 = evFromT tF (xsK.getD m []) 0 (wdK.getD j []) := by
  have h1 : gamTabs.getD m #[] = gamArr (xsData.getD m []) := by
    unfold gamTabs
    rw [KT.getD_toArray]
    interval_cases m <;> rfl
  have h2 : ∀ x, (gamArr x).getD j 0 = evI x (Wd.getD j []) := by
    intro x
    unfold gamArr
    rw [KT.getD_toArray, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getElem_range]
  rw [h1, h2, Wd_getD_eq hc hn]
  unfold evI evFrom evFromT
  simp only [mt0_getD_eq hc hn]
  rfl

theorem gamGenChk_of (hg : ((List.range 4).all fun m => (List.range 3).all fun k =>
    decide (evFromT tF (xsK.getD m []) 0 (wdK.getD (gsK.getD k 0) []) =
      (xsK.getD m []).getD k 0)) = true) : gamGenChk = true := by
  unfold gamGenChk
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hg ⊢
  intro m hm k hk
  have hj : gI.getD k 0 < 128 := by
    interval_cases k <;> decide
  rw [gamTabs_getD hc hn hm hj]
  exact hg m hm k hk

end

end CFSG.Certificates.Kernel.L5S

end
