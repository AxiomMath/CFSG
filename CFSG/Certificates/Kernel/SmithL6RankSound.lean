module

public import Certificates.Data.Kernel.SmithL6Rank

public section

namespace CFSG.SmithL6.Kernel

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

theorem getD_of_lt {α : Type} {l : List α} {s : Nat} {d : α} (h : s < l.length) :
    l.getD s d = l[s] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_of_ge {α : Type} {l : List α} {s : Nat} {d : α} (h : l.length ≤ s) :
    l.getD s d = d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem tvList_size : tvList.size = 1953 := by decide +kernel

theorem ofFn_get! {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  have h : i < (Array.ofFn f).size := by rw [Array.size_ofFn]; exact hi
  rw [getElem!_pos (Array.ofFn f) i h, Array.getElem_ofFn]

theorem get!_eq_getD {α : Type} [Inhabited α] (a : Array α) (k : Nat) :
    a[k]! = a.toList.getD k default := by
  by_cases hk : k < a.size
  · rw [getElem!_pos a k hk, getD_of_lt (by simpa using hk)]
    simp
  · rw [getElem!_neg a k hk, getD_of_ge (by simp; omega)]

theorem get0 (a : Array Nat) (k : Nat) : a[k]! = a.toList.getD k 0 := get!_eq_getD a k

theorem getA (a : Array (Array Nat)) (k : Nat) : a[k]! = a.toList.getD k #[] := get!_eq_getD a k

theorem planePtsArr_get {i : Nat} (hi : i < 1395) : planePtsArr[i]! = planePts i := by
  unfold planePtsArr
  exact ofFn_get! _ hi

theorem flagArr_get {j a : Nat} (hj : j < 1395) (ha : a < 1953) :
    flagArr[j]![a]! = inPlane j a := by
  unfold flagArr
  rw [ofFn_get! _ hj]
  exact ofFn_get! (fun a : Fin 1953 => inPlane j a.val) ha

theorem maskArr_get {i : Nat} (hi : i < 1395) : maskArr[i]! = wMask i := by
  unfold maskArr
  exact ofFn_get! _ hi

theorem annArr_get {i : Nat} (hi : i < 1395) : annArr[i]! = annK i := by
  unfold annArr
  exact ofFn_get! _ hi

theorem wtArr_get {i : Nat} (hi : i < 1395) : wtArr[i]! = wt i := by
  unfold wtArr
  exact ofFn_get! _ hi

theorem countP_range_getElem! {α : Type} [Inhabited α] (l : List α) (g : α → Bool) {n : Nat}
    (hn : l.length = n) : (List.range n).countP (fun a => g l[a]!) = l.countP g := by
  subst hn
  have e : (List.range l.length).map (fun a => l[a]!) = l := by
    refine List.ext_getElem (by simp) fun n h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    exact getElem!_pos l n h2
  conv => rhs; rw [← e]
  rw [List.countP_map]
  rfl

theorem meetCard_eq {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = meetCardK i j := by
  unfold meetCard meetCardK countMN
  rw [planePtsArr_get hi]
  unfold planePts
  rw [← Array.countP_toList, List.toList_toArray, List.countP_filter]
  have e1 : (List.range 1953).countP (fun a => flagArr[j]![a]! && inPlane i a) =
      (List.range 1953).countP (fun a => inPlane i a && inPlane j a) := by
    refine List.countP_congr fun a ha => ?_
    rw [flagArr_get hj (List.mem_range.mp ha), Bool.and_comm]
  rw [e1]
  have e3 : (fun a => inPlane i a && inPlane j a) = (fun a =>
      (fun p : Nat × Nat => (wMask i &&& wMask j).testBit p.1 && (annK i &&& annK j).testBit p.2)
        tvList.toList[a]!) := by
    funext a
    simp only [inPlane, tvPair, maskArr_get hi, maskArr_get hj, annArr_get hi, annArr_get hj,
      Nat.testBit_and, Array.getElem!_toList]
    cases (wMask i).testBit (tvList[a]!).1 <;> cases (wMask j).testBit (tvList[a]!).1 <;>
      cases (annK i).testBit (tvList[a]!).2 <;> cases (annK j).testBit (tvList[a]!).2 <;> rfl
  rw [e3]
  have hl : tvList.toList.length = 1953 := by rw [Array.length_toList, tvList_size]
  exact countP_range_getElem! tvList.toList
    (fun p : Nat × Nat => (wMask i &&& wMask j).testBit p.1 && (annK i &&& annK j).testBit p.2) hl

theorem relB_eq {R i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    relB R i j = R.testBit (distBK i j) := by
  unfold relB distB distBK
  rw [meetCard_eq hi hj]

theorem distMat_get {rr cc : List Nat} {s t : Nat} (hs : s < rr.length) (ht : t < cc.length) :
    ((distMat rr cc).getD s []).getD t 0 = distBK (rr.getD s 0) (cc.getD t 0) := by
  unfold distMat
  have e1 : (rr.map fun i => cc.map fun j => distBK i j).getD s [] =
      cc.map fun j => distBK rr[s] j := by
    rw [getD_of_lt (by rw [List.length_map]; exact hs), List.getElem_map]
  rw [e1, getD_of_lt (by rw [List.length_map]; exact ht), List.getElem_map, getD_of_lt hs,
    getD_of_lt ht]

theorem getD_lt_of_all {l : List Nat} {s : Nat} (h : l.all (· < 1395) = true) (hs : s < l.length) :
    l.getD s 0 < 1395 := by
  rw [getD_of_lt hs]
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hs))

theorem rankOK_of {R : Nat} {rr cc inv : Array Nat}
    (h1 : rr.toList.length = 21) (h2 : cc.toList.length = 21) (h3 : inv.toList.length = 21)
    (h4 : rr.toList.all (· < 1395) = true) (h5 : cc.toList.all (· < 1395) = true)
    (h6 : rankOKD R (distMat rr.toList cc.toList) inv.toList = true) :
    rankOK R rr cc inv = true := by
  unfold rankOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨by rw [← Array.length_toList]; exact h1, by rw [← Array.length_toList]; exact h2⟩,
    by rw [← Array.length_toList]; exact h3⟩,
    by rw [← Array.all_toList]; exact h4⟩, by rw [← Array.all_toList]; exact h5⟩, ?_⟩
  rw [List.all_eq_true]
  intro s hs
  have hs' : s < 21 := List.mem_range.mp hs
  have h6s := List.all_eq_true.mp h6 s hs
  rw [List.all_eq_true] at h6s ⊢
  intro u hu
  have hsu := h6s u hu
  have e : (List.range 21).foldl (fun acc t => acc ^^ (relB R rr[s]! cc[t]! && inv[t]!.testBit u))
      false = (List.range 21).foldl (fun acc t => acc ^^
        (R.testBit (((distMat rr.toList cc.toList).getD s []).getD t 0) &&
          (inv.toList.getD t 0).testBit u)) false := by
    refine congrArg (fun f => List.foldl f false (List.range 21)) ?_
    funext acc t
    rw [get0 rr s, get0 cc t, get0 inv t]
    by_cases ht : t < 21
    · rw [relB_eq (getD_lt_of_all h4 (by omega)) (getD_lt_of_all h5 (by omega)),
        distMat_get (by omega) (by omega)]
    · rw [getD_of_ge (l := inv.toList) (by omega)]
      simp only [Nat.zero_testBit, Bool.and_false, Bool.xor_false]
  rw [e]
  exact hsu

theorem chkRank_of_K (h : chkRankK = true) : chkRank = true := by
  unfold chkRankK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hr, hc⟩, hi⟩, hall⟩ := h
  unfold chkRank
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨rfl, by simpa using hr⟩, by simpa using hc⟩, by simpa using hi⟩, ?_⟩
  rw [List.all_eq_true]
  intro r hr6
  have hw := List.all_eq_true.mp hall r hr6
  unfold rankWitK at hw
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩ := hw
  rw [get0 rankRels r, getA rankRows r, getA rankCols r, getA rankInv r]
  exact rankOK_of w1 w2 w3 w4 w5 w6

theorem chkSpanW_of_K (h : chkSpanWK = true) : chkSpanW = true := by
  unfold chkSpanWK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold chkSpanW
  simp only [Bool.and_eq_true, beq_iff_eq]
  have em : spanIdx.map (fun i => wtArr[i]!) = (spanIdx.toList.map wt).toArray := by
    apply Array.ext'
    rw [Array.toList_map, List.toList_toArray]
    refine List.map_congr_left fun i hi => ?_
    exact wtArr_get (of_decide_eq_true (List.all_eq_true.mp h3 i hi))
  refine ⟨⟨⟨by simpa using h1, by simpa using h2⟩, by rw [← Array.all_toList]; exact h3⟩, ?_⟩
  rw [em]
  rw [List.all_eq_true] at h4 ⊢
  intro m hm
  rw [get0 spanCoef m]
  exact h4 m hm

end CFSG.SmithL6.Kernel
