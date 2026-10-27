module

public import Certificates.Data.Kernel.SmithEKR
public import CFSG.Certificates.Kernel.SmithEK.MSound

public section

namespace CFSG.SmithE.K

open CFSG.SmithE CFSG.F4.Native
open CFSG.SmithL6.Kernel (get0 getA getD_of_lt getD_of_ge)

theorem dRowK_cons (a m b : Nat) (P M : List Nat) :
    dRowK a m (b :: P) M = (dEntK (m &&& M.headD 0) (cntK 693 (a &&& b)) && dRowK a m P M.tail) :=
  rfl

theorem dRowK_sound {a m : Nat} : ∀ (P M : List Nat), dRowK a m P M = true →
    ∀ k < P.length, dEntK (m &&& M.getD k 0) (cntK 693 (a &&& P.getD k 0)) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | b :: P, M, h, k, hk => by
    rw [dRowK_cons, Bool.and_eq_true] at h
    cases k with
    | zero =>
      rw [getD_zero M, List.getD_cons_zero]
      exact h.1
    | succ k =>
      rw [getD_succ M, List.getD_cons_succ]
      exact dRowK_sound P M.tail h.2 k (by simpa using hk)

theorem atLeastK_eq : ∀ (k n : Nat), atLeastK k n = atLeast k n
  | 0, _ => rfl
  | k + 1, n => by
    have e : atLeastK (k + 1) n = bif n == 0 then false else atLeastK k (n &&& (n - 1)) := rfl
    rw [e, atLeast, atLeastK_eq k]
    cases h : n == 0 <;> simp [bne, h]

theorem dTailsK_succ (n : Nat) (P M : List Nat) :
    dTailsK (n + 1) P M = (dRowK (P.headD 0) (M.headD 0) P M && dTailsK n P.tail M.tail) := rfl

theorem headD_drop (l : List Nat) (k : Nat) : (l.drop k).headD 0 = l.getD k 0 := by
  rw [← getD_zero, getD_drop, Nat.add_zero]

theorem dTailsK_sound : ∀ (n : Nat) (P M : List Nat), dTailsK n P M = true → ∀ k < n,
    dRowK (P.getD k 0) (M.getD k 0) (P.drop k) (M.drop k) = true
  | 0, _, _, _, k, hk => absurd hk (by omega)
  | n + 1, P, M, h, k, hk => by
    rw [dTailsK_succ, Bool.and_eq_true] at h
    cases k with
    | zero =>
      rw [getD_zero, getD_zero]
      exact h.1
    | succ k =>
      have e := dTailsK_sound n P.tail M.tail h.2 k (by omega)
      rwa [← getD_succ, ← getD_succ, List.drop_tail, List.drop_tail] at e

theorem dChunkK_sound {P M : List Nat} {s n : Nat} (h : dChunkK P M s n = true) {i : Nat}
    (h1 : s ≤ i) (h2 : i < s + n) :
    dRowK (P.getD i 0) (M.getD i 0) (P.drop i) (M.drop i) = true := by
  have e := dTailsK_sound n _ _ h (i - s) (by omega)
  rwa [getD_drop, getD_drop, List.drop_drop, List.drop_drop, Nat.add_sub_cancel' h1] at e

theorem dEnt_of_row {P M : List Nat} (hPl : P.length = 891) {i j : Nat} (hij : i ≤ j)
    (hj : j < 891) (h : dRowK (P.getD i 0) (M.getD i 0) (P.drop i) (M.drop i) = true) :
    dEntK (M.getD i 0 &&& M.getD j 0) (cntK 693 (P.getD i 0 &&& P.getD j 0)) = true := by
  have e := dRowK_sound _ _ h (j - i) (by rw [List.length_drop, hPl]; omega)
  rwa [getD_drop, getD_drop, Nat.add_sub_cancel' hij] at e

theorem distB_eq (i j : Nat) : distB i j = distC (meetCard i j) := rfl

theorem chkDist_of {pts P M : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hPl : P.length = 891) (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts)
    (hM : ∀ i < 891, M.getD i 0 = wMask i)
    (hrow : ∀ i < 891, dRowK (P.getD i 0) (M.getD i 0) (P.drop i) (M.drop i) = true) :
    chkDist = true := by
  unfold chkDist
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hi' : i < 891 := List.mem_range.mp hi
  have hj' : j < 891 := List.mem_range.mp hj
  have hent : dEntK (M.getD i 0 &&& M.getD j 0) (cntK 693 (P.getD i 0 &&& P.getD j 0)) = true := by
    by_cases hij : i ≤ j
    · exact dEnt_of_row hPl hij hj' (hrow i hi')
    · have e := dEnt_of_row hPl (by omega : j ≤ i) hi' (hrow j hj')
      rwa [Nat.and_comm (M.getD j 0), Nat.and_comm (P.getD j 0)] at e
  have ha : adjM i j = atLeast 16 (M.getD i 0 &&& M.getD j 0) := by
    unfold adjM
    rw [maskArr_get hi', maskArr_get hj', hM i hi', hM j hj']
  dsimp only
  rw [ha, ← atLeastK_eq, distB_eq, meetCard_eq hpts hlen hP hi' hj']
  exact hent

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (L : List α) (b : β), (∀ a ∈ L, ∀ x, f x a = g x a) → L.foldl f b = L.foldl g b
  | [], _, _ => rfl
  | a :: L, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self b]
    exact foldl_congr_mem f g L _ fun a' ha' x => h a' (List.mem_cons_of_mem a ha') x

theorem foldl_xor_testBit (f : Nat → Bool) (v : Nat → Nat) (u : Nat) : ∀ (L : List Nat)
    (acc : Bool) (x : Nat), acc = x.testBit u →
    L.foldl (fun acc t => acc ^^ (f t && (v t).testBit u)) acc =
      (L.foldl (fun x t => x ^^^ bif f t then v t else 0) x).testBit u
  | [], _, _, h => h
  | t :: L, acc, x, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine foldl_xor_testBit f v u L _ _ ?_
    rw [Nat.testBit_xor, h]
    cases f t <;> simp

theorem getD_map_of_lt (l : List Nat) (f : Nat → Nat) {s : Nat} (hs : s < l.length) :
    (l.map f).getD s 0 = f (l.getD s 0) := by
  rw [getD_of_lt (by rw [List.length_map]; exact hs), List.getElem_map, getD_of_lt hs]

theorem getD_lt_891 {l : List Nat} {s : Nat} (h : l.all (· < 891) = true) (hs : s < l.length) :
    l.getD s 0 < 891 := by
  rw [getD_of_lt hs]
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hs))

theorem rankOK_of {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {R : Nat} {rr cc inv : Array Nat}
    (h : rankWitK P R rr.toList cc.toList inv.toList = true) : rankOK R rr cc inv = true := by
  unfold rankWitK rankBodyK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  unfold rankOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨by rw [← Array.length_toList]; exact h1, by rw [← Array.length_toList]; exact h2⟩,
    by rw [← Array.length_toList]; exact h3⟩,
    by rw [← Array.all_toList]; exact h4⟩, by rw [← Array.all_toList]; exact h5⟩, ?_⟩
  rw [List.all_eq_true]
  intro s hs
  have hs' : s < 21 := List.mem_range.mp hs
  have h6s := beq_iff_eq.mp (List.all_eq_true.mp h6 s hs)
  rw [List.all_eq_true]
  intro u _
  have e1 : (List.range 21).foldl (fun acc t => acc ^^ (relB R rr[s]! cc[t]! && inv[t]!.testBit u))
      false = (List.range 21).foldl (fun acc t => acc ^^
        ((fun t => relB R rr[s]! cc[t]!) t && ((fun t => inv[t]!) t).testBit u)) false := rfl
  rw [e1, foldl_xor_testBit _ _ u _ false 0 (by simp)]
  have e2 : (List.range 21).foldl (fun x t =>
      x ^^^ bif (fun t => relB R rr[s]! cc[t]!) t then (fun t => inv[t]!) t else 0) 0 =
      rowXK R ((rr.toList.map fun i => P.getD i 0).getD s 0)
        (cc.toList.map fun j => P.getD j 0) inv.toList := by
    unfold rowXK
    refine foldl_congr_mem _ _ _ _ fun t ht x => ?_
    have ht' : t < 21 := List.mem_range.mp ht
    have hr : rr.toList.getD s 0 < 891 := getD_lt_891 h4 (by omega)
    have hc : cc.toList.getD t 0 < 891 := getD_lt_891 h5 (by omega)
    dsimp only
    rw [getD_map_of_lt _ _ (by omega), getD_map_of_lt _ _ (by omega), get0 rr s, get0 cc t,
      get0 inv t]
    unfold relB
    rw [distB_eq, meetCard_eq hpts hlen hP hr hc]
  rw [e2, h6s, Nat.testBit_two_pow]
  by_cases hsu : s = u
  · subst hsu
    simp
  · simp [hsu]

theorem chkRank_of {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) (h : chkRankK P = true) :
    chkRank = true := by
  unfold chkRankK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨_, hr⟩, hc⟩, hi⟩, hall⟩ := h
  unfold chkRank
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨rfl, by simpa using hr⟩, by simpa using hc⟩, by simpa using hi⟩, ?_⟩
  rw [List.all_eq_true]
  intro r hr6
  have hw := List.all_eq_true.mp hall r hr6
  rw [get0 rankRels r, getA rankRows r, getA rankCols r, getA rankInv r]
  exact rankOK_of hpts hlen hP hw

theorem chkSpanW_of {W : List Nat} (hW : ∀ i < 891, wtArr[i]! = W.getD i 0)
    (h : chkSpanWK W = true) : chkSpanW = true := by
  unfold chkSpanWK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold chkSpanW
  simp only [Bool.and_eq_true, beq_iff_eq]
  have em : spanIdx.map (fun i => wtArr[i]!) = (spanIdx.toList.map fun i => W.getD i 0).toArray := by
    apply Array.ext'
    have e : (spanIdx.toList.map fun i => W.getD i 0).toArray.toList =
        spanIdx.toList.map fun i => W.getD i 0 := by simp
    rw [Array.toList_map, e]
    refine List.map_congr_left fun i hi => ?_
    exact hW i (of_decide_eq_true (List.all_eq_true.mp h3 i hi))
  refine ⟨⟨⟨by simpa using h1, by simpa using h2⟩, by rw [← Array.all_toList]; exact h3⟩, ?_⟩
  rw [em]
  rw [List.all_eq_true] at h4 ⊢
  intro m hm
  rw [get0 spanCoef m]
  exact h4 m hm

end CFSG.SmithE.K
