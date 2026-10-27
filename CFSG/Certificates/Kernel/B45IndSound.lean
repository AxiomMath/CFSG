module

public import Certificates.Data.Kernel.B45Ind.Defs
public import CFSG.Quasithin.Background.SmithB45MatIndDefs

public section

namespace CFSG.KC.B45Ind

open CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.H13.A5.M22Hat CFSG.Quasithin.H.Mathieu

@[expose] def LA (ts : Array (Array ℕ)) : List (List ℕ) := ts.toList.map Array.toList

theorem get!_eq {α : Type} [Inhabited α] (a : Array α) (i : ℕ) :
    a[i]! = a.toList.getD i default := by
  rcases a with ⟨l⟩
  simp [List.getD_eq_getElem?_getD]

theorem get!_nat (a : Array ℕ) (i : ℕ) : a[i]! = a.toList.getD i 0 :=
  get!_eq a i

theorem get!_pair (a : Array (ℕ × ℕ)) (i : ℕ) : a[i]! = a.toList.getD i (0, 0) :=
  get!_eq a i

theorem get!_arr (ts : Array (Array ℕ)) (i : ℕ) : ts[i]! = ((LA ts).getD i []).toArray := by
  rw [get!_eq]
  rcases ts with ⟨l⟩
  simp only [LA, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem length_LA (ts : Array (Array ℕ)) : (LA ts).length = ts.size := by
  simp [LA]

theorem comp24_eq (a b : Array ℕ) : (comp24 a b).toList = comp24L a.toList b.toList := by
  apply List.ext_getElem
  · simp [comp24, comp24L]
  · intro i h1 h2
    simp only [comp24, comp24L, Array.toList_ofFn, List.getElem_ofFn, List.getElem_map,
      List.getElem_range, get!_nat]

theorem wordArr_eq (a b : Array ℕ) (w : List Bool) :
    (wordArr a b w).toList = wordL a.toList b.toList w := by
  induction w with
  | nil => simp [wordArr, wordL, id24]
  | cons z w ih => cases z <;> simp [wordArr, wordL, comp24_eq, ih]

theorem invArr_eq (a : Array ℕ) : (invArr a).toList = invL a.toList := by
  have key : ∀ (l : List ℕ) (init : Array ℕ),
      (l.foldl (fun b i => b.set! a[i]! i) init).toList =
        l.foldl (fun b i => b.set (a.toList.getD i 0) i) init.toList := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons x l ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih]
      simp [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, get!_nat]
  simpa [invArr, invL] using key (List.range 24) (Array.replicate 24 0)

theorem LA_cosArr (a b : Array ℕ) (ws : List (List Bool)) :
    LA (cosArr a b ws) = ws.map (wordL a.toList b.toList) := by
  simp [LA, cosArr, wordArr_eq, Function.comp_def]

theorem findIdx?_arr {α : Type} (q : α → Bool) (xs : Array α) : xs.findIdx? q = xs.toList.findIdx? q := by
  rw [← List.findIdx?_toArray, Array.toArray_toList]

theorem piArr_eq (ts : Array (Array ℕ)) (g : Array ℕ) (p : ℕ) :
    (piArr ts g p).toList = piL (LA ts) g.toList p := by
  rcases ts with ⟨l⟩
  simp only [piArr, piL, LA, List.map_toArray, List.findIdx?_toArray, Array.toList_map,
    List.map_map, get!_nat, comp24_eq, Function.comp_def]

theorem hArr_eq (ts : Array (Array ℕ)) (g pi : Array ℕ) :
    LA (hArr ts g pi) = hL (LA ts) g.toList pi.toList := by
  simp only [hArr, hL, LA, Array.toList_map, Array.toList_range, List.map_map, List.length_map,
    Array.length_toList]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, comp24_eq, invArr_eq, get!_nat, get!_arr, List.toList_toArray]
  rfl

theorem piOK_eq (ts : Array (Array ℕ)) (g : Array ℕ) (p : ℕ) (pi : Array ℕ) :
    piOK ts g p pi = piOKL (LA ts) g.toList p pi.toList := by
  simp only [piOK, piOKL, length_LA, get!_nat, get!_arr, List.toList_toArray, comp24_eq]

theorem cosetOK_eq (a b : Array ℕ) (ts : Array (Array ℕ)) (m p : ℕ) :
    cosetOK a b ts m p = cosetOKL a.toList b.toList (LA ts) m p := by
  simp only [cosetOK, cosetOKL, piOK_eq, piArr_eq, length_LA, get!_nat, get!_arr,
    List.toList_toArray, invArr_eq]

theorem indCols_eq (d : ℕ) (Xc : Array ℕ → ℕ → ℕ) (ts : Array (Array ℕ)) (g : Array ℕ) (p : ℕ) :
    indCols d Xc ts g p = indColsL d Xc (LA ts) g.toList p := by
  simp only [indCols, indColsL, ← piArr_eq, ← hArr_eq, length_LA, get!_nat, get!_arr]

theorem scanIdx_find {α : Type} (q : α → Bool) (i : ℕ) :
    ∀ (l : List α) (k : ℕ) (f : ℕ → α), (∀ j (h : j < l.length), f (k + j) = l[j]) →
      (List.range' k l.length).find? (fun j => decide (i ≤ j) && q (f j)) = scanIdx q i k l
  | [], _, _, _ => rfl
  | e :: l, k, f, hf => by
    have h0 : f k = e := hf 0 (by simp)
    have ih := scanIdx_find q i l (k + 1) f fun j h => by
      have := hf (j + 1) (by simpa using h)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this
    simp only [List.length_cons, List.range'_succ, List.find?_cons, scanIdx, h0, ih]
    cases decide (i ≤ k) && q e <;> rfl

theorem mapIdxFrom_eq {α β : Type} (f : ℕ → α → β) :
    ∀ (l : List α) (k : ℕ), mapIdxFrom f k l = l.mapIdx fun i => f (k + i)
  | [], _ => rfl
  | e :: l, k => by
    rw [mapIdxFrom, List.mapIdx_cons, mapIdxFrom_eq f l (k + 1)]
    congr 2
    funext i
    rw [Nat.add_assoc, Nat.add_comm 1 i]

theorem swap_eq (st : Array (ℕ × ℕ)) (i j : ℕ) :
    (st.swapIfInBounds i j).toList = swapL st.toList i j := by
  unfold Array.swapIfInBounds swapL
  simp only [Array.length_toList]
  by_cases h1 : i < st.size
  · by_cases h2 : j < st.size
    · rw [dif_pos h1, dif_pos h2, Array.toList_swap, if_pos ⟨h1, h2⟩,
        List.getD_eq_getElem _ _ (by simpa using h2), List.getD_eq_getElem _ _ (by simpa using h1)]
      rfl
    · rw [dif_pos h1, dif_neg h2, if_neg fun h => h2 h.2]
  · rw [dif_neg h1, if_neg fun h => h1 h.1]

theorem invStep_size (n : ℕ) (st : Array (ℕ × ℕ)) (i : ℕ) : (invStep n st i).size = st.size := by
  unfold invStep
  split <;> simp

theorem invStep_eq (st : Array (ℕ × ℕ)) (i : ℕ) :
    (invStep st.size st i).toList = invStepL st.toList i := by
  have hf : (List.range st.size).find? (fun j => decide (i ≤ j) && (st[j]!).1.testBit i) =
      pivL st.toList i := by
    rw [List.range_eq_range', ← Array.length_toList]
    simp only [get!_pair]
    exact scanIdx_find (fun e : ℕ × ℕ => e.1.testBit i) i st.toList 0
      (fun j => st.toList.getD j (0, 0)) fun j h => by rw [Nat.zero_add, List.getD_eq_getElem _ _ h]
  unfold invStep invStepL
  rw [hf]
  rcases pivL st.toList i with _ | j
  · rfl
  · simp only [Array.toList_mapIdx, swap_eq, get!_pair, mapIdxFrom_eq, Nat.zero_add]

theorem invCols_eq (n : ℕ) (P : List ℕ) : invCols n P = invColsL n P := by
  have key : ∀ (l : List ℕ) (st : Array (ℕ × ℕ)), st.size = n →
      (l.foldl (invStep n) st).toList = l.foldl invStepL st.toList := by
    intro l
    induction l with
    | nil => intro st _; rfl
    | cons x l ih =>
      intro st h
      rw [List.foldl_cons, List.foldl_cons, ih _ (by rw [invStep_size, h]), ← h, invStep_eq]
  unfold invCols invColsL
  dsimp only
  rw [key _ _ (by simp)]
  simp

end CFSG.KC.B45Ind
