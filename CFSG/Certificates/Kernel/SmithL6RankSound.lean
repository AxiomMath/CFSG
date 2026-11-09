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

@[expose] def countMN (M N : Nat) : Nat :=
  tvList.toList.countP fun p => M.testBit p.1 && N.testBit p.2

theorem par_xorP (x y : Nat) : par (x ^^^ y) = (par x ^^ par y) := by
  simp only [par, List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
    List.foldl_nil, List.foldl_append, Nat.testBit_xor, Bool.false_xor]
  simp only [Bool.xor_assoc, Bool.xor_left_comm]

theorem form_xor (φ x y : Nat) : form φ (x ^^^ y) = (form φ x ^^ form φ y) := by
  unfold form
  rw [Nat.and_xor_distrib_left, par_xorP]

theorem form_zeroP (φ : Nat) : form φ 0 = false := by
  unfold form
  rw [Nat.and_zero]
  rfl

theorem testBit_foldl_orP (g : Nat → Nat) (n : Nat) :
    ∀ (l : List Nat) (acc : Nat), (l.foldl (fun acc d => acc ||| 2 ^ g d) acc).testBit n =
      (acc.testBit n || l.any fun d => g d == n)
  | [], acc => by simp
  | d :: l, acc => by
    rw [List.foldl_cons, testBit_foldl_orP g n l, Nat.testBit_or, Nat.testBit_two_pow,
      List.any_cons, Bool.or_assoc]
    congr 2

theorem testBit_foldl_if (P : Nat → Bool) (n : Nat) :
    ∀ (l : List Nat) (acc : Nat),
      (l.foldl (fun acc φ => if P φ then acc ||| 2 ^ φ else acc) acc).testBit n =
        (acc.testBit n || l.any fun φ => P φ && φ == n)
  | [], acc => by simp
  | d :: l, acc => by
    rw [List.foldl_cons, testBit_foldl_if P n l, List.any_cons]
    cases hP : P d
    · simp
    · simp only [↓reduceIte]
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc, Bool.true_and]
      congr 2

theorem form_of_mem (i v φ : Nat) (hv : (wMask i).testBit v = true)
    (hφ : (annK i).testBit φ = true) : form φ v = false := by
  unfold wMask annK at *
  generalize wB i = W at hv hφ
  obtain ⟨a, b, c⟩ := W
  simp only [spanMask] at hv
  simp only [annMaskOf] at hφ
  rw [testBit_foldl_orP, Nat.zero_testBit, Bool.false_or, List.any_eq_true] at hv
  rw [testBit_foldl_if, Nat.zero_testBit, Bool.false_or, List.any_eq_true] at hφ
  obtain ⟨d, -, hd⟩ := hv
  obtain ⟨ψ, -, hψ⟩ := hφ
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hψ
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, rfl⟩ := hψ
  rw [← beq_iff_eq.mp hd, form_xor, form_xor]
  cases d.testBit 0 <;> cases d.testBit 1 <;> cases d.testBit 2 <;>
    simp [ha, hb, hc, form_zeroP]

theorem countP_range_mul (f g : Nat → Bool) : ∀ a : Nat,
    (List.range (a * 64)).countP (fun n => f (n / 64) && g (n % 64)) =
      (List.range a).countP f * (List.range 64).countP g
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, List.range_add, List.countP_append, countP_range_mul f g a, List.countP_map,
      List.range_succ (n := a), List.countP_append]
    have e : (List.range 64).countP ((fun n => f (n / 64) && g (n % 64)) ∘ (a * 64 + ·)) =
        (List.range 64).countP (fun k => f a && g k) := by
      refine List.countP_congr fun k hk => ?_
      have hk := List.mem_range.mp hk
      have e1 : (a * 64 + k) / 64 = a := by omega
      have e2 : (a * 64 + k) % 64 = k := by omega
      simp only [Function.comp_apply, e1, e2]
    rw [e]
    cases h : f a <;> simp [h, Nat.add_mul]

theorem popKP_eq : ∀ (k m : Nat), popKP k m = (List.range k).countP fun v => m.testBit v
  | 0, _ => rfl
  | k + 1, m => by
    rw [popKP, popKP_eq k (m / 2), List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have e : ((fun v => m.testBit v) ∘ Nat.succ) = fun v => (m / 2).testBit v :=
      funext fun v => Nat.testBit_succ m v
    rw [e, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega

theorem cnt64_eq (M : Nat) :
    cnt64 M = (List.range 64).countP fun v => v != 0 && M.testBit v := by
  rw [cnt64, popKP_eq, List.range_succ_eq_map (n := 63), List.countP_cons, List.countP_map]
  have e : ((fun v => v != 0 && M.testBit v) ∘ Nat.succ) = fun v => (M / 2).testBit v :=
    funext fun v => by simp [Nat.testBit_succ]
  rw [e]
  rfl

theorem countMNP_eq {i M N : Nat} (hM : ∀ v, M.testBit v = true → (wMask i).testBit v = true)
    (hN : ∀ φ, N.testBit φ = true → (annK i).testBit φ = true) :
    countMN M N = cnt64 M * cnt64 N := by
  rw [cnt64_eq, cnt64_eq]
  unfold countMN
  have h4 : (4096 : Nat) = 64 * 64 := rfl
  rw [tvList, List.toList_toArray, List.countP_filterMap, h4, ← countP_range_mul]
  refine List.countP_congr fun n _ => ?_
  dsimp only
  by_cases hv : n / 64 = 0
  · simp [hv]
  by_cases hφ : n % 64 = 0
  · simp [hφ]
  cases hMv : M.testBit (n / 64) <;> cases hNφ : N.testBit (n % 64)
  · cases form (n % 64) (n / 64) <;> simp [hv, hφ, hMv, hNφ]
  · cases form (n % 64) (n / 64) <;> simp [hv, hφ, hMv, hNφ]
  · cases form (n % 64) (n / 64) <;> simp [hv, hφ, hMv, hNφ]
  · have hf := form_of_mem i _ _ (hM _ hMv) (hN _ hNφ)
    simp [hv, hφ, hMv, hNφ, hf]

theorem meetCardK_eq (i j : Nat) :
    meetCardK i j = countMN (wMask i &&& wMask j) (annK i &&& annK j) := by
  unfold meetCardK
  refine (countMNP_eq (i := i) (fun v hv => ?_) (fun φ hφ => ?_)).symm
  · rw [Nat.testBit_and, Bool.and_eq_true] at hv
    exact hv.1
  · rw [Nat.testBit_and, Bool.and_eq_true] at hφ
    exact hφ.1

theorem meetCard_eq {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = meetCardK i j := by
  rw [meetCardK_eq]
  unfold meetCard countMN
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
