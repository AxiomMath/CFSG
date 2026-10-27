module

public import Certificates.Data.Kernel.E64F
public import CFSG.Quasithin.Vol2.KGFactE64Inputs
public import Mathlib.Data.List.Sort

public section

namespace CFSG.KC.E64F

open CFSG.Quasithin.H13.KGE64 CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def Good (n : Nat) (t : Array Nat) (f : Nat → Nat) : Prop :=
  t.size = n ∧ ∀ p < n, t.getD p 0 = f p ∧ f p < n

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem fa_append {α β : Type} {R : α → β → Prop} {l1 m1 : List α} {l2 m2 : List β}
    (h1 : List.Forall₂ R l1 l2) (h2 : List.Forall₂ R m1 m2) : List.Forall₂ R (l1 ++ m1) (l2 ++ m2) := by
  induction h1 with
  | nil => exact h2
  | cons r _ ih => exact List.Forall₂.cons r ih

theorem fa_filter {α β : Type} {R : α → β → Prop} {P : α → Bool} {Q : β → Bool}
    (hPQ : ∀ a b, R a b → P a = Q b) {l1 : List α} {l2 : List β} (h : List.Forall₂ R l1 l2) :
    List.Forall₂ R (l1.filter P) (l2.filter Q) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b _ _ r _ ih =>
    rw [List.filter_cons, List.filter_cons, hPQ a b r]
    cases Q b
    · exact ih
    · exact List.Forall₂.cons r ih

theorem fa_all {α β : Type} {R : α → β → Prop} {P : α → Bool} {Q : β → Bool}
    (hPQ : ∀ a b, R a b → P a = Q b) {l1 : List α} {l2 : List β} (h : List.Forall₂ R l1 l2) :
    l1.all P = l2.all Q := by
  induction h with
  | nil => rfl
  | @cons a b _ _ r _ ih => rw [List.all_cons, List.all_cons, hPQ a b r, ih]

theorem getD_map_arr {t : Array Nat} {h : Nat → Nat} {p : Nat} (hp : p < t.size) :
    (t.map h).getD p 0 = h (t.getD p 0) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hp]

theorem wordImg_eq {n : Nat} {ltabs : Array (Array Nat)} {L : Nat → Nat → Nat}
    (hL : ∀ l < ltabs.size, Good n (ltabs.getD l #[]) (L l)) :
    ∀ w : List Nat, (∀ l ∈ w, l < ltabs.size) → ∀ p < n,
      wordImg ltabs w p = wordF L w p ∧ wordF L w p < n
  | [], _, p, hp => ⟨rfl, hp⟩
  | l :: w, hw, p, hp => by
    obtain ⟨e, h⟩ := wordImg_eq hL w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) p hp
    have hl := hL l (hw l List.mem_cons_self)
    change (ltabs.getD l #[]).getD (wordImg ltabs w p) 0 = L l (wordF L w p) ∧
      L l (wordF L w p) < n
    rw [e]
    exact hl.2 _ h

theorem good_word {n : Nat} {ltabs : Array (Array Nat)} {L : Nat → Nat → Nat}
    (hL : ∀ l < ltabs.size, Good n (ltabs.getD l #[]) (L l)) {w : List Nat}
    (hw : ∀ l ∈ w, l < ltabs.size) : Good n (wordTabA ltabs n w) (wordF L w) := by
  refine ⟨by simp [wordTabA], fun p hp => ?_⟩
  have e : (wordTabA ltabs n w).getD p 0 = wordImg ltabs w p := by
    simp [wordTabA, Array.getD_eq_getD_getElem?, hp]
  rw [e]
  exact wordImg_eq hL w hw p hp

theorem good_mul {n : Nat} {s t : Array Nat} {g f : Nat → Nat} (hs : Good n s g) (ht : Good n t f) :
    Good n (tMul s t) (fun p => g (f p)) := by
  refine ⟨by simp [tMul, ht.1], fun p hp => ?_⟩
  rw [tMul, getD_map_arr (by rw [ht.1]; exact hp), (ht.2 p hp).1]
  exact hs.2 _ (ht.2 p hp).2

theorem good_id (n : Nat) : Good n (tId n) (fun p => p) := by
  refine ⟨by simp [tId], fun p hp => ⟨?_, hp⟩⟩
  simp [tId, Array.getD_eq_getD_getElem?, hp]

theorem good_pow {n : Nat} {y : Array Nat} {f : Nat → Nat} (hy : Good n y f) :
    ∀ k, Good n (tPow n y k) f^[k]
  | 0 => good_id n
  | k + 1 => by
    have e : f^[k + 1] = fun p => f (f^[k] p) := funext fun p => Function.iterate_succ_apply' f k p
    rw [e]
    exact good_mul hy (good_pow hy k)

theorem powers_getD (n : Nat) (y : Array Nat) {i : Nat} (hi : i < 8) :
    (powers n y).getD i #[] = tPow n y i := by
  simp [powers, Array.getD_eq_getD_getElem?, hi]

theorem ev_eq {n : Nat} {ts : List (Array Nat)} {fs : List (Nat → Nat)}
    (h : List.Forall₂ (Good n) ts fs) : ∀ p < n, ev ts p = evF fs p ∧ evF fs p < n := by
  induction h with
  | nil => exact fun p hp => ⟨rfl, hp⟩
  | @cons t f ts fs r _ ih =>
    intro p hp
    obtain ⟨e, hl⟩ := ih p hp
    change t.getD (ev ts p) 0 = f (evF fs p) ∧ f (evF fs p) < n
    rw [e]
    exact r.2 _ hl

theorem isId_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {ts : List (Array Nat)}
    {fs : List (Nat → Nat)} (h : List.Forall₂ (Good n) ts fs) : isId B ts = isIdF B fs := by
  unfold isId isIdF
  exact all_congr' fun p hp => by rw [(ev_eq h p (hB p hp)).1]

theorem eqOn_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {us vs : List (Array Nat)}
    {fu fv : List (Nat → Nat)} (hu : List.Forall₂ (Good n) us fu)
    (hv : List.Forall₂ (Good n) vs fv) : eqOn B us vs = eqOnF B fu fv := by
  unfold eqOn eqOnF
  exact all_congr' fun p hp => by rw [(ev_eq hu p (hB p hp)).1, (ev_eq hv p (hB p hp)).1]

theorem fa_replicate {n : Nat} {y : Array Nat} {f : Nat → Nat} (hy : Good n y f) :
    ∀ k, List.Forall₂ (Good n) (List.replicate k y) (List.replicate k f)
  | 0 => List.Forall₂.nil
  | k + 1 => List.Forall₂.cons hy (fa_replicate hy k)

theorem fa_cj {n : Nat} {pw : Array (Array Nat)} {Y : Nat → Nat}
    (hpw : ∀ i < 8, Good n (pw.getD i #[]) Y^[i]) {a : Array Nat} {fa : Nat → Nat}
    (ha : Good n a fa) {i : Nat} (hi : i < 8) : List.Forall₂ (Good n) (cj pw a i) (cjF Y fa i) :=
  List.Forall₂.cons (hpw i hi) (List.Forall₂.cons ha (List.Forall₂.cons (hpw (7 - i) (by omega))
    List.Forall₂.nil))

theorem condA_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {pw : Array (Array Nat)}
    {Y : Nat → Nat} (hpw : ∀ i < 8, Good n (pw.getD i #[]) Y^[i]) {a : Array Nat} {fa : Nat → Nat}
    (ha : Good n a fa) : condA B pw a = condAF B Y fa := by
  unfold condA condAF
  rw [isId_eq hB (List.Forall₂.cons ha List.Forall₂.nil),
    isId_eq hB (List.Forall₂.cons ha (List.Forall₂.cons ha List.Forall₂.nil)),
    isId_eq hB (fa_append (fa_append (fa_cj hpw ha (by omega)) (fa_cj hpw ha (by omega)))
      (List.Forall₂.cons ha List.Forall₂.nil))]

theorem condB_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {pw : Array (Array Nat)}
    {Y : Nat → Nat} (hpw : ∀ i < 8, Good n (pw.getD i #[]) Y^[i]) {a : Array Nat} {fa : Nat → Nat}
    (ha : Good n a fa) : condB B pw a = condBF B Y fa := by
  unfold condB condBF
  rw [isId_eq hB (List.Forall₂.cons ha List.Forall₂.nil),
    isId_eq hB (List.Forall₂.cons ha (List.Forall₂.cons ha List.Forall₂.nil)),
    isId_eq hB (fa_append (fa_append (fa_cj hpw ha (by omega)) (fa_cj hpw ha (by omega)))
      (List.Forall₂.cons ha List.Forall₂.nil))]

theorem commAll_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {pw : Array (Array Nat)}
    {Y : Nat → Nat} (hpw : ∀ i < 8, Good n (pw.getD i #[]) Y^[i]) {a b : Array Nat}
    {fa fb : Nat → Nat} (ha : Good n a fa) (hb : Good n b fb) :
    commAll B pw a b = commAllF B Y fa fb := by
  unfold commAll commAllF
  refine all_congr' fun i hi => all_congr' fun j hj => ?_
  rw [List.mem_range] at hi hj
  exact eqOn_eq hB (fa_append (fa_cj hpw ha (by omega)) (fa_cj hpw hb (by omega)))
    (fa_append (fa_cj hpw hb (by omega)) (fa_cj hpw ha (by omega)))

theorem pairCheck_eq {n : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < n) {y : Array Nat}
    {fy : Nat → Nat} (hy : Good n y fy) {ts : List (Array Nat)} {fs : List (Nat → Nat)}
    (hts : List.Forall₂ (Good n) ts fs) : pairCheck n B y ts = pairCheckF B fy fs := by
  unfold pairCheck pairCheckF
  refine all_congr' fun k _ => ?_
  have hpw : ∀ i < 8, Good n ((powers n (tPow n y k)).getD i #[]) (fy^[k])^[i] := by
    intro i hi
    rw [powers_getD n _ hi]
    exact good_pow (good_pow hy k) i
  dsimp only
  refine fa_all (fun a fa ha => ?_) (fa_filter (fun a fa ha => condA_eq hB hpw ha) hts)
  refine fa_all (fun b fb hb => ?_) (fa_filter (fun b fb hb => condB_eq hB hpw hb) hts)
  rw [commAll_eq hB hpw ha hb]

theorem insO_eq (a : Nat) : ∀ l : List Nat, insO a l = l.orderedInsert (· ≤ ·) a
  | [] => by
    rw [List.orderedInsert_nil]
    rfl
  | b :: l => by
    change (bif Nat.ble a b then a :: b :: l else b :: insO a l) = _
    rw [insO_eq a l, List.orderedInsert_cons]
    cases hb : Nat.ble a b with
    | false =>
      have h : ¬ a ≤ b := by
        rw [← Nat.ble_eq, hb]
        decide
      rw [if_neg h]
      rfl
    | true =>
      have h : a ≤ b := by
        rw [← Nat.ble_eq, hb]
      rw [if_pos h]
      rfl

theorem insN_eq : ∀ l : List Nat, insN l = List.insertionSort (· ≤ ·) l
  | [] => by
    rw [List.insertionSort_nil]
    rfl
  | a :: l => by
    change insO a (insN l) = _
    rw [insO_eq, insN_eq l, List.insertionSort_cons]

theorem sortN_eq (l : List Nat) : sortN l = insN l := by
  rw [insN_eq]
  exact List.mergeSort_eq_insertionSort (r := (· ≤ ·)) l

theorem e64_sound {n : Nat} {B : List Nat} {ltabs : Array (Array Nat)} {L : Nat → Nat → Nat}
    {yw : List Nat} {ows labels : List (List Nat)}
    (hL : ∀ l < ltabs.size, Good n (ltabs.getD l #[]) (L l)) (hB : ∀ b ∈ B, b < n)
    (hlab : ∀ Lb ∈ labels, ∀ p ∈ Lb, p < n)
    (h : e64CheckF B L ltabs.size yw ows labels = true) :
    e64Check n B ptAct ltabs yw ows labels = true := by
  unfold e64CheckF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hw1 : ∀ l ∈ yw, l < ltabs.size := by simpa using h1
  have hw2 : ∀ w ∈ ows, ∀ l ∈ w, l < ltabs.size := by simpa using h2
  have hy := good_word hL hw1
  have hts : List.Forall₂ (Good n) (ows.map (wordTabA ltabs n)) (ows.map (wordF L)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w hw => good_word hL (hw2 w hw)
  unfold e64Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [isId_eq hB (fa_replicate hy 7)]
    exact h3
  · rw [isId_eq hB (List.Forall₂.cons hy List.Forall₂.nil)]
    exact h4
  · have e : ((ows.map (wordTabA ltabs n)).map fun t => B.map fun p => t.getD p 0) =
        ows.map fun w => B.map (wordF L w) := by
      rw [List.map_map]
      exact List.map_congr_left fun w hw => List.map_congr_left fun p hp =>
        ((good_word hL (hw2 w hw)).2 p (hB p hp)).1
    rw [e]
    exact h5
  · rw [List.all_map]
    rw [← h6]
    refine all_congr' fun w hw => all_congr' fun Lb hLb => ?_
    have e : Lb.map (fun p => (wordTabA ltabs n w).getD p 0) = Lb.map (wordF L w) :=
      List.map_congr_left fun p hp => ((good_word hL (hw2 w hw)).2 p (hlab Lb hLb p hp)).1
    simp only [Function.comp, ptAct, e, sortN_eq]
  · rw [pairCheck_eq hB hy hts]
    exact h7

end CFSG.KC.E64F

end
