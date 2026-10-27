module

public import Certificates.Data.CFSGNative.J1.Vec
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KS.GI

open CFSG.Sporadic.J1.Native CFSG.KS.SporSch.LyM CFSG.Sporadic.He.Native

abbrev MR := Array (Array Nat) × Array (Array Nat)

@[expose] def gElim (p c : Nat) (mc rc : Array Nat) (s : MR) (i : Nat) : MR :=
  if (i != c && (s.1[i]!)[c]! % p != 0) = true then
    (s.1.set! i (Array.zipWith (fun x y => (x + (p - (s.1[i]!)[c]! % p) * y) % p) s.1[i]! mc),
      s.2.set! i (Array.zipWith (fun x y => (x + (p - (s.1[i]!)[c]! % p) * y) % p) s.2[i]! rc))
  else s

@[expose] def gStep (p d : Nat) (s : MR) (c : Nat) : MR :=
  if pivF p d c s.1 < d then
    (List.range d).foldl (gElim p c
        (s.1[pivF p d c s.1]!.map fun x => x * invMod p ((s.1[pivF p d c s.1]!)[c]! % p) % p)
        (s.2[pivF p d c s.1]!.map fun x => x * invMod p ((s.1[pivF p d c s.1]!)[c]! % p) % p))
      ((((s.1.set! (pivF p d c s.1) s.1[c]!).set! c s.1[pivF p d c s.1]!).set! c
          (s.1[pivF p d c s.1]!.map fun x => x * invMod p ((s.1[pivF p d c s.1]!)[c]! % p) % p)),
        (((s.2.set! (pivF p d c s.1) s.2[c]!).set! c s.2[pivF p d c s.1]!).set! c
          (s.2[pivF p d c s.1]!.map fun x => x * invMod p ((s.1[pivF p d c s.1]!)[c]! % p) % p)))
  else s

theorem gaussInv_fold (p d : Nat) (X : List (List Nat)) : gaussInv p d X =
    (((List.range d).foldl (gStep p d) ((X.map fun (r : List Nat) => r.toArray).toArray,
      ((idL d).map fun (r : List Nat) => r.toArray).toArray)).2.map fun row => row.toList).toList := by
  unfold gaussInv
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yieldL,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

@[expose] def RowS (p d : Nat) (a mi ri : Array Nat) : Prop :=
  a.size = 2 * d ∧ mi.size = d ∧ ri.size = d ∧
    ∀ j < d, a[j]! = mi[j]! ∧ a[d + j]! = ri[j]! ∧ mi[j]! < p ∧ ri[j]! < p

@[expose] def Sim (p d : Nat) (m r A : Array (Array Nat)) : Prop :=
  A.size = d ∧ m.size = d ∧ r.size = d ∧ ∀ i < d, RowS p d A[i]! m[i]! r[i]!

theorem set_sim {p d i : Nat} {m r A : Array (Array Nat)} {a mi ri : Array Nat}
    (h : Sim p d m r A) (hr : RowS p d a mi ri) :
    Sim p d (m.set! i mi) (r.set! i ri) (A.set! i a) := by
  obtain ⟨hA, hm, hr', hrow⟩ := h
  refine ⟨by rw [size_setR, hA], by rw [size_setR, hm], by rw [size_setR, hr'], fun k hk => ?_⟩
  rw [get_setR _ _ _ (by omega), get_setR _ _ _ (by omega), get_setR _ _ _ (by omega)]
  by_cases e : k = i
  · rw [ite_eq_left e, ite_eq_left e, ite_eq_left e]
    exact hr
  · rw [ite_eq_right e, ite_eq_right e, ite_eq_right e]
    exact hrow k hk

theorem swap_sim {p d piv c : Nat} {m r A : Array (Array Nat)} (h : Sim p d m r A)
    (hp : piv < d) (hc : c < d) : Sim p d (swapR m piv c) (swapR r piv c) (swapR A piv c) := by
  unfold swapR
  exact set_sim (set_sim h (h.2.2.2 c hc)) (h.2.2.2 piv hp)

theorem sim_col {p d c : Nat} {m r A : Array (Array Nat)} (h : Sim p d m r A) (hc : c < d) :
    ∀ i < d, (A[i]!)[c]! = (m[i]!)[c]! := fun i hi => ((h.2.2.2 i hi).2.2.2 c hc).1

theorem foldl_congr' {β γ : Type} (f g : β → γ → β) (l : List γ) (b : β)
    (h : ∀ x ∈ l, ∀ y, f y x = g y x) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self b]
    exact ih _ (fun z hz y => h z (List.mem_cons_of_mem x hz) y)

theorem pivF_congr {p d c : Nat} {A m : Array (Array Nat)}
    (h : ∀ i < d, (A[i]!)[c]! = (m[i]!)[c]!) : pivF p d c A = pivF p d c m := by
  unfold pivF
  refine foldl_congr' _ _ _ _ fun x hx y => ?_
  rw [List.mem_range'_1] at hx
  unfold pivS
  rw [h x (by omega)]

theorem get_map' {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} {f : α → β} {j : Nat}
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := get_mapR a f hj

theorem scale_sim {p d c : Nat} (hp : 0 < p) {m r A : Array (Array Nat)} (h : Sim p d m r A)
    (hc : c < d) :
    Sim p d (m.set! c (m[c]!.map fun x => x * invMod p ((m[c]!)[c]! % p) % p))
      (r.set! c (r[c]!.map fun x => x * invMod p ((m[c]!)[c]! % p) % p)) (scaleR p c A) := by
  obtain ⟨ha, hm, hr, hrow⟩ := (id h : Sim p d m r A).2.2.2 c hc
  unfold scaleR
  refine set_sim h ⟨by simp [ha], by simp [hm], by simp [hr], fun j hj => ?_⟩
  obtain ⟨e1, e2, l1, l2⟩ := hrow j hj
  have hcc := hrow c hc
  have hiv : (A[c]!)[c]! ^ (p - 2) % p = invMod p ((m[c]!)[c]! % p) := by
    unfold invMod
    rw [hcc.1, Nat.mod_eq_of_lt hcc.2.2.1]
  rw [get_map' (by omega), get_map' (by omega), get_map' (by omega), get_map' (by omega), hiv,
    e1, e2]
  exact ⟨rfl, rfl, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

theorem gelim_fold {p d c : Nat} {mc rc : Array Nat} {m r : Array (Array Nat)} (hm : m.size = d)
    (hr : r.size = d) :
    ∀ n ≤ d, ((List.range n).foldl (gElim p c mc rc) (m, r)).1.size = d ∧
      ((List.range n).foldl (gElim p c mc rc) (m, r)).2.size = d ∧
      ∀ i < d, ((List.range n).foldl (gElim p c mc rc) (m, r)).1[i]! =
          (if i < n ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0 then
            Array.zipWith (fun x y => (x + (p - (m[i]!)[c]! % p) * y) % p) m[i]! mc else m[i]!) ∧
        ((List.range n).foldl (gElim p c mc rc) (m, r)).2[i]! =
          (if i < n ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0 then
            Array.zipWith (fun x y => (x + (p - (m[i]!)[c]! % p) * y) % p) r[i]! rc else r[i]!) := by
  intro n
  induction n with
  | zero => intro _; simp [hm, hr]
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hM : (List.range n).foldl (gElim p c mc rc) (m, r) = M at ih1 ih2 ih3 ⊢
    have hn1 : M.1[n]! = m[n]! := by rw [(ih3 n (by omega)).1]; simp
    have hn2 : M.2[n]! = r[n]! := by rw [(ih3 n (by omega)).2]; simp
    have lt_iff : ∀ i, (i < n + 1 ∧ i ≠ n) ↔ i < n := fun i => by omega
    unfold gElim
    by_cases hcond : n ≠ c ∧ (m[n]!)[c]! % p ≠ 0
    · have e : (n != c && (M.1[n]!)[c]! % p != 0) = true := by
        rw [hn1]
        simpa using hcond
      rw [ite_eq_left e]
      refine ⟨by rw [size_setR, ih1], by rw [size_setR, ih2], fun i hi => ?_⟩
      rw [get_setR _ _ _ (by rw [ih1]; exact hi), get_setR _ _ _ (by rw [ih2]; exact hi)]
      by_cases hin : i = n
      · subst hin
        rw [ite_eq_left rfl, ite_eq_left rfl, hn1, hn2, ite_eq_left ⟨by omega, hcond⟩, ite_eq_left ⟨by omega, hcond⟩]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hin, ite_eq_right hin, (ih3 i hi).1, (ih3 i hi).2]
        have e2 : (i < n ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) ↔
            (i < n + 1 ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) := by omega
        simp only [e2]
        exact ⟨trivial, trivial⟩
    · have e : ¬ (n != c && (M.1[n]!)[c]! % p != 0) = true := by
        rw [hn1]
        simpa using hcond
      rw [ite_eq_right e]
      refine ⟨ih1, ih2, fun i hi => ?_⟩
      rw [(ih3 i hi).1, (ih3 i hi).2]
      by_cases hin : i = n
      · subst hin
        have e3 : ¬ (i < i + 1 ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) := fun h' => hcond ⟨h'.2.1, h'.2.2⟩
        rw [ite_eq_right e3, ite_eq_right e3, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact ⟨rfl, rfl⟩
      · have e2 : (i < n ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) ↔
            (i < n + 1 ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) := by omega
        simp only [e2]
        exact ⟨trivial, trivial⟩

theorem zipWith_get {f : Nat → Nat → Nat} {a b : Array Nat} {j : Nat} (ha : j < a.size)
    (hb : j < b.size) : (Array.zipWith f a b)[j]! = f a[j]! b[j]! := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_zipWith, getElem!_pos a j ha,
    getElem!_pos b j hb]

theorem newRow_get {p d c : Nat} {A : Array (Array Nat)} {i j : Nat} (hj : j < 2 * d) :
    (newRow p d c A i)[j]! = ((A[i]!)[j]! + (p - (A[i]!)[c]!) * (A[c]!)[j]!) % p := by
  unfold newRow
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem elim_sim {p d c : Nat} (hp : 0 < p) {m r A : Array (Array Nat)} (h : Sim p d m r A)
    (hc : c < d) :
    Sim p d ((List.range d).foldl (gElim p c m[c]! r[c]!) (m, r)).1
      ((List.range d).foldl (gElim p c m[c]! r[c]!) (m, r)).2
      ((List.range d).foldl (elimS p d c) A) := by
  obtain ⟨hA, hm, hr, hrow⟩ := h
  obtain ⟨g1, g2, g3⟩ := gelim_fold (p := p) (c := c) (mc := m[c]!) (rc := r[c]!) hm hr d (Nat.le_refl _)
  obtain ⟨f1, f2⟩ := elim_fold p d c A hA hc d (Nat.le_refl _)
  refine ⟨f1, g1, g2, fun i hi => ?_⟩
  rw [(g3 i hi).1, (g3 i hi).2, f2 i hi]
  obtain ⟨a1, a2, a3, a4⟩ := hrow i hi
  obtain ⟨c1, c2, c3, c4⟩ := hrow c hc
  have hci := (a4 c hc)
  have hmod : (m[i]!)[c]! % p = (m[i]!)[c]! := Nat.mod_eq_of_lt hci.2.2.1
  have hiff : (i < d ∧ i ≠ c ∧ (A[i]!)[c]! ≠ 0) ↔ (i < d ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0) := by
    rw [hmod, hci.1]
  by_cases hcond : i < d ∧ i ≠ c ∧ (m[i]!)[c]! % p ≠ 0
  · rw [ite_eq_left (hiff.2 hcond), ite_eq_left hcond, ite_eq_left hcond]
    refine ⟨by simp [newRow], by simp [a2, c2], by simp [a3, c3], fun j hj => ?_⟩
    obtain ⟨e1, e2, l1, l2⟩ := a4 j hj
    obtain ⟨k1, k2, -, -⟩ := c4 j hj
    rw [newRow_get (by omega), newRow_get (by omega), zipWith_get (by omega) (by omega),
      zipWith_get (by omega) (by omega), e1, e2, k1, k2, hci.1, hmod]
    exact ⟨rfl, rfl, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩
  · rw [ite_eq_right (fun h' => hcond (hiff.1 h')), ite_eq_right hcond, ite_eq_right hcond]
    exact hrow i hi

theorem step_sim {p d c : Nat} (hp : 0 < p) {s : MR} {A : Array (Array Nat)}
    (h : Sim p d s.1 s.2 A) (hc : c < d) : Sim p d (gStep p d s c).1 (gStep p d s c).2 (stepS p d A c) := by
  have hpv : pivF p d c A = pivF p d c s.1 := pivF_congr (sim_col h hc)
  unfold gStep stepS
  rw [hpv]
  by_cases hlt : pivF p d c s.1 < d
  · rw [ite_eq_left hlt, ite_eq_left hlt]
    generalize pivF p d c s.1 = piv at hlt
    have hs := swap_sim h hlt hc
    have hsc := scale_sim hp hs hc
    have e1 : (swapR s.1 piv c)[c]! = s.1[piv]! := by rw [swap_get h.2.1 hc, ite_eq_left rfl]
    have e2 : (swapR s.2 piv c)[c]! = s.2[piv]! := by rw [swap_get h.2.2.1 hc, ite_eq_left rfl]
    rw [e1, e2] at hsc
    have hel := elim_sim hp hsc hc
    have e3 : ((swapR s.1 piv c).set! c (s.1[piv]!.map fun x =>
        x * invMod p ((s.1[piv]!)[c]! % p) % p))[c]! =
        s.1[piv]!.map fun x => x * invMod p ((s.1[piv]!)[c]! % p) % p := by
      rw [get_setR _ _ _ (by unfold swapR; rw [size_setR, size_setR, h.2.1]; exact hc), ite_eq_left rfl]
    have e4 : ((swapR s.2 piv c).set! c (s.2[piv]!.map fun x =>
        x * invMod p ((s.1[piv]!)[c]! % p) % p))[c]! =
        s.2[piv]!.map fun x => x * invMod p ((s.1[piv]!)[c]! % p) % p := by
      rw [get_setR _ _ _ (by unfold swapR; rw [size_setR, size_setR, h.2.2.1]; exact hc), ite_eq_left rfl]
    rw [e3, e4] at hel
    exact hel
  · rw [ite_eq_right hlt, ite_eq_right hlt]
    exact h

theorem toArr_size (L : List (List Nat)) : ((L.map fun (r : List Nat) => r.toArray).toArray).size = L.length := by
  simp

theorem toArr_get (L : List (List Nat)) (i j : Nat) :
    (((L.map fun (r : List Nat) => r.toArray).toArray)[i]!)[j]! = (L.getD i []).getD j 0 := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · rw [getElem!_pos _ i (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp only [List.getElem_toArray, List.getElem_map]
    rcases Nat.lt_or_ge j L[i].length with hj | hj
    · rw [getElem!_pos _ j (by simpa using hj), List.getD_eq_getElem _ _ hj]
      simp
    · rw [getElem!_neg _ j (by simp; omega), List.getD_eq_default _ _ hj]
      rfl
  · rw [getElem!_neg _ i (by simp; omega), List.getD_eq_default _ _ hi]
    have e : (default : Array Nat) = #[] := rfl
    rw [e]
    simp

theorem toArr_row_size (L : List (List Nat)) (i : Nat) (hi : i < L.length) :
    (((L.map fun (r : List Nat) => r.toArray).toArray)[i]!).size = (L.getD i []).length := by
  rw [getElem!_pos _ i (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem idL_getD {d i j : Nat} (hi : i < d) (hj : j < d) :
    ((idL d).getD i []).getD j 0 = if i = j then 1 else 0 := by
  unfold idL
  simp [List.getD_eq_getElem?_getD, hi, hj]

theorem idL_length (d : Nat) : (idL d).length = d := by simp [idL]

theorem idL_row_length {d i : Nat} (hi : i < d) : ((idL d).getD i []).length = d := by
  unfold idL
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem wf_facts {p d : Nat} {X : List (List Nat)}
    (hX : wfM d X = true ∧ X.all (fun r => r.all fun x => decide (x < p)) = true) :
    X.length = d ∧ (∀ i < d, (X.getD i []).length = d) ∧
      ∀ i < d, ∀ j < d, (X.getD i []).getD j 0 < p := by
  obtain ⟨h1, h2⟩ := hX
  unfold wfM at h1
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  simp only [List.all_eq_true, decide_eq_true_eq] at h2
  refine ⟨h1.1, fun i hi => ?_, fun i hi j hj => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)]
    exact h1.2 _ (List.getElem_mem _)
  · have hl : i < X.length := by omega
    rw [List.getD_eq_getElem _ _ hl]
    have hr := h1.2 _ (List.getElem_mem hl)
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h2 _ (List.getElem_mem hl) _ (List.getElem_mem _)

theorem init_sim {p d : Nat} (hp : 2 ≤ p) {X : List (List Nat)}
    (hX : wfM d X = true ∧ X.all (fun r => r.all fun x => decide (x < p)) = true) :
    Sim p d ((X.map fun (r : List Nat) => r.toArray).toArray) ((idL d).map fun (r : List Nat) => r.toArray).toArray
      (initG p d ((X.map fun (r : List Nat) => r.toArray).toArray)) := by
  obtain ⟨hl, hrl, hlt⟩ := wf_facts hX
  refine ⟨by simp [initG], by rw [toArr_size, hl], by rw [toArr_size, idL_length], fun i hi => ?_⟩
  refine ⟨?_, by rw [toArr_row_size _ _ (by omega), hrl i hi],
    by rw [toArr_row_size _ _ (by rw [idL_length]; exact hi), idL_row_length hi], fun j hj => ?_⟩
  · unfold initG
    rw [ofFn_get! _ hi]
    simp
  · have g1 : ((initG p d ((X.map fun (r : List Nat) => r.toArray).toArray))[i]!)[j]! =
        (X.getD i []).getD j 0 := by
      unfold initG
      rw [ofFn_get! _ hi, ofFn_get! _ (by omega)]
      simp only [hj, ↓reduceIte]
      rw [toArr_get, Nat.mod_eq_of_lt (hlt i hi j hj)]
    have g2 : ((initG p d ((X.map fun (r : List Nat) => r.toArray).toArray))[i]!)[d + j]! =
        if i = j then 1 else 0 := by
      unfold initG
      rw [ofFn_get! _ hi, ofFn_get! _ (by omega)]
      simp only [Nat.not_lt.2 (Nat.le_add_right d j), ↓reduceIte, Nat.add_sub_cancel_left]
      by_cases e : i = j
      · simp [e]
      · simp [e, Ne.symm e]
    rw [g1, g2, toArr_get, toArr_get, idL_getD hi hj]
    refine ⟨rfl, rfl, hlt i hi j hj, ?_⟩
    split <;> omega

theorem dotL_eq {d : Nat} : ∀ {a b : List Nat}, a.length = d → b.length = d →
    dotL a b = ∑ k ∈ Finset.range d, a.getD k 0 * b.getD k 0 := by
  induction d with
  | zero =>
    intro a b ha hb
    rw [List.length_eq_zero_iff.1 ha]
    rfl
  | succ d ih =>
    intro a b ha hb
    match a, b, ha, hb with
    | x :: a, y :: b, ha, hb =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [← ih ha hb, Nat.add_comm]
      rfl

theorem prod_facts {p d : Nat} {X Y : List (List Nat)}
    (hX : wfM d X = true ∧ X.all (fun r => r.all fun x => decide (x < p)) = true)
    (hY : wfM d Y = true ∧ Y.all (fun r => r.all fun x => decide (x < p)) = true)
    (h : mulL p d Y X = idL d) :
    ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, (((X.getD i []).getD k 0 : Nat) : ZMod p) *
      (((Y.getD k []).getD j 0 : Nat) : ZMod p) = if i = j then 1 else 0 := by
  obtain ⟨hXl, hXr, -⟩ := wf_facts hX
  obtain ⟨hYl, hYr, -⟩ := wf_facts hY
  have hYX : ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, (((Y.getD i []).getD k 0 : Nat) : ZMod p) *
      (((X.getD k []).getD j 0 : Nat) : ZMod p) = if i = j then 1 else 0 := by
    intro i hi j hj
    have e := congrArg (fun M => (M.getD i []).getD j 0) h
    beta_reduce at e
    rw [idL_getD hi hj] at e
    unfold mulL at e
    rw [List.getD_eq_getElem (List.map _ Y) _ (by simp; omega), List.getElem_map,
      List.getD_eq_getElem (List.map _ (colsL d X)) _ (by simp [colsL]; omega),
      List.getElem_map] at e
    have hcol : (colsL d X)[j]'(by simp [colsL]; omega) = X.map fun r => r.getD j 0 := by
      simp [colsL]
    rw [hcol, dotL_eq (d := d) (by rw [← List.getD_eq_getElem _ []]; exact hYr i hi)
      (by simp [hXl])] at e
    have e2 := congrArg (fun n : Nat => (n : ZMod p)) e
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e2
    rw [← List.getD_eq_getElem _ []] at e2
    refine Eq.trans (Finset.sum_congr rfl fun k hk => ?_) (e2.trans ?_)
    · rw [List.getD_eq_getElem (X.map fun r => r.getD j 0) 0
        (by rw [List.length_map, hXl]; exact Finset.mem_range.1 hk), List.getElem_map,
        ← List.getD_eq_getElem _ []]
    · split <;> simp
  let Mx : Matrix (Fin d) (Fin d) (ZMod p) := fun i j => (((X.getD i.val []).getD j.val 0 : Nat) : ZMod p)
  let My : Matrix (Fin d) (Fin d) (ZMod p) := fun i j => (((Y.getD i.val []).getD j.val 0 : Nat) : ZMod p)
  have h1 : My * Mx = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e := hYX i.val i.isLt j.val j.isLt
    rw [Finset.sum_range] at e
    rw [e]
    simp [Fin.ext_iff]
  have h2 : Mx * My = 1 := mul_eq_one_comm.1 h1
  intro i hi j hj
  have e := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at e
  rw [Finset.sum_range]
  refine e.trans ?_
  simp [Fin.ext_iff]

theorem gaussInv_spec {p d : Nat} {X Y : List (List Nat)} (hp : p.Prime)
    (hX : wfM d X = true ∧ X.all (fun r => r.all fun x => decide (x < p)) = true)
    (hY : wfM d Y = true ∧ Y.all (fun r => r.all fun x => decide (x < p)) = true)
    (h : mulL p d Y X = idL d) : gaussInv p d X = Y := by
  have hp2 := hp.two_le
  obtain ⟨hYl, hYr, hYp⟩ := wf_facts hY
  have hsim : ∀ n ≤ d, Sim p d
      ((List.range n).foldl (gStep p d) ((X.map fun (r : List Nat) => r.toArray).toArray,
        ((idL d).map fun (r : List Nat) => r.toArray).toArray)).1
      ((List.range n).foldl (gStep p d) ((X.map fun (r : List Nat) => r.toArray).toArray,
        ((idL d).map fun (r : List Nat) => r.toArray).toArray)).2
      ((List.range n).foldl (stepS p d) (initG p d ((X.map fun (r : List Nat) => r.toArray).toArray))) := by
    intro n
    induction n with
    | zero => intro _; exact init_sim hp2 hX
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      exact step_sim (by omega) (ih (by omega)) (by omega)
  have hS := hsim d (Nat.le_refl _)
  generalize hR : (List.range d).foldl (gStep p d) ((X.map fun (r : List Nat) => r.toArray).toArray,
    ((idL d).map fun (r : List Nat) => r.toArray).toArray) = R at hS
  have hinv := invM_spec (d := d) hp (X := (X.map fun (r : List Nat) => r.toArray).toArray)
    (y := fun i j => (Y.getD i []).getD j 0) (fun i hi j hj => hYp i hi j hj) (fun i hi j hj => by
      have := prod_facts hX hY h i hi j hj
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) this
      rw [toArr_get])
  rw [invM_eq_invF] at hinv
  unfold invF at hinv
  obtain ⟨hA, -, hr, hrow⟩ := hS
  generalize (List.range d).foldl (stepS p d) (initG p d ((X.map fun (r : List Nat) => r.toArray).toArray)) = A
    at hA hrow hinv
  have hent : ∀ i < d, ∀ j < d, (R.2[i]!)[j]! = (Y.getD i []).getD j 0 := by
    intro i hi j hj
    have e := congrArg (fun B : Array (Array Nat) => (B[i]!)[j]!) hinv
    beta_reduce at e
    rw [ofFn_get! _ hi, ofFn_get! _ hj, get_mapR _ _ (by omega)] at e
    obtain ⟨a1, -, -, a4⟩ := hrow i hi
    rw [← (a4 j hj).2.1, ← e, getElem!_pos _ j (by simp [a1]; omega),
      getElem!_pos _ (d + j) (by omega), Array.getElem_extract]
  rw [gaussInv_fold, hR]
  apply List.ext_getElem (by simp [hr, hYl])
  intro i h1 h2
  have hi : i < d := by simpa [hr] using h1
  simp only [Array.getElem_toList, Array.getElem_map]
  obtain ⟨-, -, a3, -⟩ := hrow i hi
  rw [← getElem!_pos R.2 i (by omega)]
  have hYi : Y[i] = Y.getD i [] := (List.getD_eq_getElem _ _ (by omega)).symm
  have hYil : (Y.getD i []).length = d := hYr i hi
  rw [hYi]
  apply List.ext_getElem (by rw [Array.length_toList, a3, hYil])
  intro j k1 k2
  have hj : j < d := by rw [hYil] at k2; exact k2
  rw [Array.getElem_toList, ← getElem!_pos _ j (by omega), hent i hi j hj,
    List.getD_eq_getElem _ 0 (by rw [hYil]; exact hj)]

end CFSG.KS.GI

end
