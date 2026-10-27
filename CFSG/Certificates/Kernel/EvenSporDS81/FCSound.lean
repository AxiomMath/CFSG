module

public import Certificates.Data.Kernel.EvenSporDS81.FCDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCSpec
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.EvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem insN_eq (a : Nat) : ∀ l : List Nat, insN a l = l.orderedInsert (· ≤ ·) a
  | [] => (List.orderedInsert_nil _ _).symm
  | b :: l => by simp only [insN, List.orderedInsert_cons, insN_eq a l]

theorem isortN_eq : ∀ l : List Nat, isortN l = l.insertionSort (· ≤ ·)
  | [] => by simp [isortN]
  | b :: l => by simp only [isortN, List.insertionSort_cons, isortN_eq l, insN_eq]

theorem arr_findIdx {α : Type} (xs : Array α) (p : α → Bool) :
    xs.findIdx p = xs.toList.findIdx p := by
  rw [← List.findIdx_toArray, Array.toArray_toList]

theorem arr_getElem! {α : Type} [Inhabited α] (xs : Array α) (i : Nat) :
    xs[i]! = xs.toList.getD i default := by
  rcases xs with ⟨l⟩
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem mergeSort_eq_isortN (l : List Nat) : l.mergeSort (fun a b => decide (a ≤ b)) = isortN l := by
  rw [isortN_eq]
  exact List.mergeSort_eq_insertionSort (r := (· ≤ ·)) l

theorem getElem!_getElem!_eq_getT (tab : Array (Array Nat)) (i j : Nat) :
    tab[i]![j]! = getT (tab.toList.map Array.toList) i j := by
  unfold getT
  rw [arr_getElem!, arr_getElem! tab,
    show ([] : List Nat) = Array.toList (default : Array Nat) from rfl, List.getD_map]
  rfl

theorem fcMatEqAct_fcAct {m a r : Array Nat} (hr : fcColsLt r = true) :
    fcMatEqAct m (fcAct a) r = fcMatEqLin m a r := by
  have h := fcColsLt_iff.1 hr
  simp only [fcMatEqAct, fcMatEqLin, fcAct_getElem! (h 0 (by omega)), fcAct_getElem! (h 1 (by omega)),
    fcAct_getElem! (h 2 (by omega)), fcAct_getElem! (h 3 (by omega)),
    fcAct_getElem! (h 4 (by omega)), fcAct_getElem! (h 5 (by omega)),
    fcAct_getElem! (h 6 (by omega)), fcAct_getElem! (h 7 (by omega)),
    fcAct_getElem! (h 8 (by omega)), fcAct_getElem! (h 9 (by omega))]

theorem fcMul_eq {ms : Array (Array Nat)} (h : ms.toList.all fcColsLt = true) :
    (fcMul ms (ms.map fcAct)).toList.map Array.toList = tabL ms.toList := by
  have hm : ∀ r ∈ ms.toList, fcColsLt r = true := List.all_eq_true.1 h
  unfold fcMul tabL
  simp only [Array.toList_map, List.map_map, Function.comp_def, arr_findIdx]
  refine List.map_congr_left fun a _ => List.map_congr_left fun r hr => ?_
  congr 1
  funext m
  exact fcMatEqAct_fcAct (hm r hr)

theorem colK_zero {x y : Nat} (hx : x < 1024) : colK (x + 1024 * y) 0 = x := by
  simp only [colK]; omega

theorem colK_succ (x y i : Nat) (hx : x < 1024) : colK (x + 1024 * y) (i + 1) = colK y i := by
  simp only [colK]
  congr 1
  omega

theorem colK_keyA {c : Array Nat} (h : ∀ i < 10, c[i]! < 1024) {i : Nat} (hi : i < 10) :
    colK (keyA c) i = c[i]! := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega); have h8 := h 8 (by omega)
  have h9 := h 9 (by omega)
  have z9 : colK c[9]! 0 = c[9]! := by simp only [colK]; omega
  unfold keyA
  interval_cases i <;>
    simp only [colK_succ _ _ _ h0, colK_succ _ _ _ h1, colK_succ _ _ _ h2, colK_succ _ _ _ h3,
      colK_succ _ _ _ h4, colK_succ _ _ _ h5, colK_succ _ _ _ h6, colK_succ _ _ _ h7,
      colK_succ _ _ _ h8, colK_zero h0, colK_zero h1, colK_zero h2, colK_zero h3, colK_zero h4,
      colK_zero h5, colK_zero h6, colK_zero h7, colK_zero h8, z9]

theorem foldr_mem_congr {l : List Nat} {f g : Nat → Nat → Nat}
    (h : ∀ i ∈ l, ∀ acc, f i acc = g i acc) (b : Nat) : l.foldr f b = l.foldr g b := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [h i List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem linK_keyA {c : Array Nat} (h : ∀ i < 10, c[i]! < 1024) (v : Nat) :
    linK (keyA c) v = lin c v := by
  unfold linK lin linL
  exact foldr_mem_congr (fun i hi acc => by rw [colK_keyA h (List.mem_range.1 hi)]) 0

theorem prodK_keyA {a r : Array Nat} (ha : ∀ i < 10, a[i]! < 1024)
    (hr : ∀ i < 10, r[i]! < 1024) : prodK (keyA a) (keyA r) = keyA (composeK a r) := by
  unfold prodK
  simp only [colK_keyA hr (by omega : 0 < 10), colK_keyA hr (by omega : 1 < 10),
    colK_keyA hr (by omega : 2 < 10), colK_keyA hr (by omega : 3 < 10),
    colK_keyA hr (by omega : 4 < 10), colK_keyA hr (by omega : 5 < 10),
    colK_keyA hr (by omega : 6 < 10), colK_keyA hr (by omega : 7 < 10),
    colK_keyA hr (by omega : 8 < 10), colK_keyA hr (by omega : 9 < 10), linK_keyA ha]
  rfl

theorem keyA_eq_iff {m p : Array Nat} (hm : ∀ i < 10, m[i]! < 1024)
    (hp : ∀ i < 10, p[i]! < 1024) : keyA m = keyA p ↔ ∀ i < 10, m[i]! = p[i]! := by
  constructor
  · intro e i hi
    rw [← colK_keyA hm hi, ← colK_keyA hp hi, e]
  · intro e
    unfold keyA
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
      e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega)]

theorem composeK_lt {a r : Array Nat} (ha : ∀ i < 10, a[i]! < 1024) :
    ∀ i < 10, (composeK a r)[i]! < 1024 := by
  intro i hi
  interval_cases i <;> exact lin_lt a ha _

theorem fcMatEqLin_iff {m a r : Array Nat} :
    fcMatEqLin m a r = true ↔ ∀ i < 10, m[i]! = (composeK a r)[i]! := by
  constructor
  · intro h i hi
    simp only [fcMatEqLin, Bool.and_eq_true, beq_iff_eq] at h
    interval_cases i <;> simp_all [composeK]
  · intro h
    simp only [fcMatEqLin, Bool.and_eq_true, beq_iff_eq]
    have e := fun i hi => h i hi
    simp only [composeK] at e
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨e 0 (by omega), e 1 (by omega)⟩, e 2 (by omega)⟩, e 3 (by omega)⟩,
      e 4 (by omega)⟩, e 5 (by omega)⟩, e 6 (by omega)⟩, e 7 (by omega)⟩, e 8 (by omega)⟩,
      e 9 (by omega)⟩

theorem findIdx_eq_idxOf {l : List (Array Nat)} {p : Array Nat → Bool} {f : Array Nat → Nat}
    {y : Nat} (h : ∀ m ∈ l, p m = (f m == y)) : l.findIdx p = (l.map f).idxOf y := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [List.findIdx_cons, List.map_cons, List.idxOf_cons, h m List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem tabL_eq_tabK {ms : List (Array Nat)} (h : ms.all fcColsLt = true) :
    tabL ms = tabK (ms.map keyA) := by
  have hb : ∀ m ∈ ms, ∀ i < 10, m[i]! < 1024 := fun m hm =>
    fcColsLt_iff.1 (List.all_eq_true.1 h m hm)
  unfold tabL tabK
  simp only [List.map_map, Function.comp_def]
  refine List.map_congr_left fun a ha => ?_
  refine List.map_congr_left fun r hr => ?_
  rw [prodK_keyA (hb a ha) (hb r hr)]
  refine findIdx_eq_idxOf fun m hm => ?_
  rw [Bool.eq_iff_iff, fcMatEqLin_iff, beq_iff_eq,
    keyA_eq_iff (hb m hm) (composeK_lt (hb a ha))]

theorem idCols_eq : idCols = idColsK := by
  apply Array.ext (by simp [idCols, idColsK])
  intro i h1 _
  simp only [idCols, Array.size_ofFn] at h1
  simp only [idCols, Array.getElem_ofFn, idColsK]
  interval_cases i <;> rfl

theorem fcIdx_eq (ms : Array (Array Nat)) (r : Array Nat) : fcIdx ms r = idxL ms.toList r := by
  simp only [fcIdx, idxL, arr_findIdx]

theorem fcIdx_fun (ms : Array (Array Nat)) : fcIdx ms = idxL ms.toList :=
  funext (fcIdx_eq ms)

theorem tabAll_eq (tab : Array (Array Nat)) (n : Nat) :
    tab.all (·.all (· < n)) = (tab.toList.map Array.toList).all (·.all (· < n)) := by
  simp only [← Array.all_toList, List.all_map, Function.comp_def]

theorem fcHits_eq (ia : Array Nat) (n : Nat) : fcHits ia n = hitsL ia.toList n := by
  simp [fcHits, hitsL, Array.contains_toList]

theorem fcCover_eq (tab : Array (Array Nat)) (A B : List Nat) (n : Nat) :
    fcCover tab A B n = coverL (tab.toList.map Array.toList) A B n := by
  simp only [fcCover, coverL, getElem!_getElem!_eq_getT]

theorem fcExt_eq (tab : Array (Array Nat)) (Y : List Nat) (y : Nat) :
    fcExt tab Y y = extL (tab.toList.map Array.toList) Y y := by
  simp only [fcExt, extL, getElem!_getElem!_eq_getT, mergeSort_eq_isortN]

theorem fcExtOK_eq (tab : Array (Array Nat)) (e n : Nat) (fam : List (List Nat)) :
    fcExtOK tab e n fam = extOKL (tab.toList.map Array.toList) e n fam := by
  simp only [fcExtOK, extOKL, getElem!_getElem!_eq_getT, fcExt_eq]

theorem act_get (ms : Array (Array Nat)) (x : Nat) {v : Nat} (hv : v < 1024) :
    (ms.map fcAct)[x]![v]! = lin (ms.toList.getD x #[]) v := by
  rw [arr_getElem! (ms.map fcAct), Array.toList_map]
  rcases Nat.lt_or_ge x ms.toList.length with hx | hx
  · rw [List.getD_eq_getElem _ _ (by simpa using hx), List.getD_eq_getElem _ _ hx,
      List.getElem_map, fcAct_getElem! hv]
  · rw [List.getD_eq_default _ _ (by simpa using hx), List.getD_eq_default _ _ hx]
    have h0 : ∀ l : List Nat, linL #[] v l = 0 := fun l => by
      induction l with
      | nil => rfl
      | cons j l ih => simp [linL, ih]
    rw [arr_getElem!]
    change ([] : List Nat).getD v 0 = linL #[] v (List.range 10)
    rw [h0]
    rfl

theorem fcFix_eq (ms : Array (Array Nat)) (Z : List Nat) :
    fcFix (ms.map fcAct) Z = fixL ms.toList Z := by
  unfold fcFix fixL
  exact congrArg List.length (List.filter_congr fun v hv => by
    simp only [act_get ms _ (List.mem_range.1 hv)])

theorem fcFixOK_eq (ms : Array (Array Nat)) (e : Nat) (fam : List (List Nat)) :
    fcFixOK (ms.map fcAct) e fam = fixOKL ms.toList e fam := by
  simp only [fcFixOK, fixOKL, fcFix_eq]

theorem axFixOK_eq (ms : Array (Array Nat)) (q : Nat → Bool) (fam : List (List Nat)) :
    axFixOK (ms.map fcAct) q fam = axFixOKL ms.toList q fam := by
  simp only [axFixOK, axFixOKL, fcFix_eq]

theorem all_of_slices {α : Type} (p : α → Bool) (k : Nat) :
    ∀ (n : Nat) (l : List α), l.length ≤ k * n →
      (∀ c < n, ((l.drop (k * c)).take k).all p = true) → l.all p = true
  | 0, l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [this]
  | n + 1, l, hl, h => by
    rw [← List.take_append_drop k l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_slices p k n (l.drop k) ?_ fun c hc => ?_⟩
    · simp only [List.length_drop]
      rw [Nat.mul_succ] at hl
      omega
    · have := h (c + 1) (by omega)
      rwa [List.drop_drop, show k + k * c = k * (c + 1) by rw [Nat.mul_succ, Nat.add_comm]]

theorem tabAllL_fcMul {ms : Array (Array Nat)} (hms : ms.toList.all fcColsLt = true)
    (hT : tabAllL (tabK (ms.toList.map keyA)) ms.size = true) :
    ((fcMul ms (Array.map fcAct ms)).toList.all fun a => a.toList.all fun x =>
      decide (x < ms.size)) = true := by
  rw [← tabL_eq_tabK hms, ← fcMul_eq hms, tabAllL, List.all_map] at hT
  exact hT

theorem fcCheck_of_twin {cu cw ms : Array (Array Nat)} {fam : List (List Nat)}
    (hms : ms.toList.all fcColsLt = true)
    (h1 : fcRestL cu.toList cw.toList ms.toList fam (tabK (ms.toList.map keyA)) = true)
    (hT : tabAllL (tabK (ms.toList.map keyA)) ms.size = true) (h2 : fcDistinct ms = true)
    (h3 : fixOKL ms.toList (idxL ms.toList idColsK) fam = true) :
    fcCheck cu cw ms fam = true := by
  unfold fcCheck fcCore
  simp only [fcExtOK_eq, fcCover_eq, tabAll_eq, fcFixOK_eq, fcHits_eq, ← Array.all_toList,
    Array.toList_map, fcIdx_fun, idCols_eq]
  have hT' := tabAllL_fcMul hms hT
  rw [fcMul_eq hms, tabL_eq_tabK hms]
  simp only [fcRestL, Array.length_toList] at h1 h3
  simp only [Array.length_toList, h2, h3, hT', Bool.and_true, Bool.true_and]
  simp only [Bool.and_eq_true] at h1 ⊢
  tauto

theorem axCheck_of_twin {ms : Array (Array Nat)} {qs : Array Bool} {fam : List (List Nat)}
    (hms : ms.toList.all fcColsLt = true)
    (h1 : axRestL ms.toList fam (tabK (ms.toList.map keyA)) = true)
    (hT : tabAllL (tabK (ms.toList.map keyA)) ms.size = true) (h2 : fcDistinct ms = true)
    (h3 : axFixOKL ms.toList (fun k => qs[k]!) fam = true) :
    axCheck ms qs fam = true := by
  unfold axCheck axCore
  simp only [fcExtOK_eq, tabAll_eq, axFixOK_eq, ← Array.all_toList, fcIdx_fun, idCols_eq]
  have hT' := tabAllL_fcMul hms hT
  rw [fcMul_eq hms, tabL_eq_tabK hms]
  simp only [axRestL, Array.length_toList] at h1
  simp only [Array.length_toList, h2, h3, hT', Bool.and_true, Bool.true_and]
  simp only [Bool.and_eq_true] at h1 ⊢
  tauto

theorem compose_eq (c c' : Array Nat) : compose c c' = composeK c c' := by
  apply Array.ext (by simp [compose, composeK])
  intro i h1 _
  simp only [compose, Array.size_ofFn] at h1
  simp only [compose, Array.getElem_ofFn, composeK]
  interval_cases i <;> rfl

theorem axWordCols_eq (gc : Array (Array Nat)) (w : List Nat) :
    axWordCols gc w = axWordColsK gc w := by
  simp only [axWordCols, axWordColsK, compose_eq, idCols_eq]

theorem axWordsOK_of_twin {gc : Array (Array Nat)} {qs : Array Bool} {ws : Array (List Nat)}
    {ms : Array (Array Nat)} (h : axWordsOKL gc qs ws ms = true) : axWordsOK gc qs ws ms = true := by
  simpa only [axWordsOK, axWordsOKL, axWordCols_eq, ← Array.all_toList] using h

end CFSG.KC.EvenSporDS81
