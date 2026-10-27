module

public import Certificates.Data.Kernel.E64L
public import CFSG.Quasithin.Vol2.KGFactE64Inputs
public import Certificates.Data.Kernel.SporLatDcCode
public import CFSG.Certificates.Kernel.E64FSound

public section

namespace CFSG.KC.E64L

open CFSG.Quasithin.H13.KGE64 CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem getD_arr (t : Array Nat) (p : Nat) : t.getD p 0 = t.toList.getD p 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem getD_arrA (A : Array (Array Nat)) (l : Nat) :
    (A.getD l #[]).toList = (A.toList.map Array.toList).getD l [] := by
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases A[l]? <;> rfl

theorem wordImg_eqT (tabs : Array (Array Nat)) (w : List Nat) (p : Nat) :
    wordImg tabs w p = wordImgT (tabs.toList.map Array.toList) w p := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    unfold wordImg wordImgT
    rw [List.foldr_cons, List.foldr_cons]
    unfold wordImg wordImgT at ih
    rw [ih, getD_arr, getD_arrA]

theorem wordTabA_eqT (tabs : Array (Array Nat)) (n : Nat) (w : List Nat) :
    (wordTabA tabs n w).toList = wordTabT (tabs.toList.map Array.toList) n w := by
  simp [wordTabA, wordTabT, wordImg_eqT]

theorem tMul_eqT (s t : Array Nat) : (tMul s t).toList = tMulT s.toList t.toList := by
  simp [tMul, tMulT, getD_arr]

theorem tPow_eqT (n : Nat) (y : Array Nat) : ∀ k, (tPow n y k).toList = tPowT n y.toList k
  | 0 => by simp [tPow, tPowT, tId]
  | k + 1 => by rw [tPow, tPowT, tMul_eqT, tPow_eqT n y k]

theorem powers_eqT (n : Nat) (y : Array Nat) :
    (powers n y).toList.map Array.toList = powersT n y.toList := by
  simp [powers, powersT, tPow_eqT]

theorem ev_eqT (ts : List (Array Nat)) (p : Nat) : ev ts p = evT (ts.map Array.toList) p := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold ev evT
    rw [List.map_cons, List.foldr_cons, List.foldr_cons]
    unfold ev evT at ih
    rw [ih, getD_arr]

theorem isId_eqT (B : List Nat) (ts : List (Array Nat)) :
    isId B ts = isIdT B (ts.map Array.toList) := by
  simp [isId, isIdT, ev_eqT]

theorem eqOn_eqT (B : List Nat) (us vs : List (Array Nat)) :
    eqOn B us vs = eqOnT B (us.map Array.toList) (vs.map Array.toList) := by
  simp [eqOn, eqOnT, ev_eqT]

theorem cj_eqT (pw : Array (Array Nat)) (a : Array Nat) (i : Nat) :
    (cj pw a i).map Array.toList = cjT (pw.toList.map Array.toList) a.toList i := by
  simp [cj, cjT, getD_arrA]

theorem condA_eqT (B : List Nat) (pw : Array (Array Nat)) (a : Array Nat) :
    condA B pw a = condAT B (pw.toList.map Array.toList) a.toList := by
  simp only [condA, condAT, isId_eqT, List.map_append, cj_eqT, List.map_cons, List.map_nil]

theorem condB_eqT (B : List Nat) (pw : Array (Array Nat)) (a : Array Nat) :
    condB B pw a = condBT B (pw.toList.map Array.toList) a.toList := by
  simp only [condB, condBT, isId_eqT, List.map_append, cj_eqT, List.map_cons, List.map_nil]

theorem commAll_eqT (B : List Nat) (pw : Array (Array Nat)) (a b : Array Nat) :
    commAll B pw a b = commAllT B (pw.toList.map Array.toList) a.toList b.toList := by
  simp only [commAll, commAllT, eqOn_eqT, List.map_append, cj_eqT]

theorem all_all_eq {α : Type} (l m : List α) (g : α → α → Bool) :
    (l.all fun a => m.all (g a)) = (l.isEmpty || m.isEmpty || l.all fun a => m.all (g a)) := by
  cases l <;> cases m <;> simp

theorem pairCheck_eqT (n : Nat) (B : List Nat) (y : Array Nat) (ts : List (Array Nat)) :
    pairCheck n B y ts = (List.range' 1 6).all (pairKT n B y.toList (ts.map Array.toList)) := by
  unfold pairCheck pairKT
  refine all_congr' fun k _ => ?_
  rw [all_all_eq]
  have eA : condA B (powers n (tPow n y k)) =
      fun a => condAT B (powersT n (tPowT n y.toList k)) a.toList := by
    funext a
    rw [condA_eqT, powers_eqT, tPow_eqT]
  have eB : condB B (powers n (tPow n y k)) =
      fun a => condBT B (powersT n (tPowT n y.toList k)) a.toList := by
    funext a
    rw [condB_eqT, powers_eqT, tPow_eqT]
  simp only [eA, eB, commAll_eqT, powers_eqT, tPow_eqT, List.filter_map, List.all_map,
    List.isEmpty_map, Function.comp_def]

theorem codeAT_eqT (n : Nat) (t : Array Nat) : CFSG.KC.SLDc.codeAT n t = codeATL n t.toList := by
  funext c
  simp [CFSG.KC.SLDc.codeAT, codeATL, getD_arr]

theorem codeSetT_eqT (n : Nat) (t : Array Nat) (x : List Nat) :
    CFSG.KC.SLDc.codeSetT n t x = codeSetTL n t.toList x := by
  rw [CFSG.KC.SLDc.codeSetT, codeSetTL, codeAT_eqT]

theorem e64Check_eqT {Lab : Type} [DecidableEq Lab] (n : Nat) (B : List Nat)
    (act : Array Nat → Lab → Lab) (actL : List Nat → Lab → Lab)
    (hact : ∀ t L, act t L = actL t.toList L) (ltabs : Array (Array Nat)) (yw : List Nat)
    (ows : List (List Nat)) (labels : List Lab) :
    e64Check n B act ltabs yw ows labels =
      e64CheckT n B actL (ltabs.toList.map Array.toList) yw ows labels := by
  unfold e64Check e64CheckT
  simp only [List.length_map, Array.length_toList, isId_eqT, List.map_replicate, List.map_cons,
    List.map_nil, pairCheck_eqT, List.map_map, Function.comp_def, getD_arr, hact, List.all_map,
    wordTabA_eqT]

end CFSG.KC.E64L

end
