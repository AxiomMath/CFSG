module

public import CFSG.Certificates.Kernel.Spor.PK.ChainSim

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

@[expose] def lvAt (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) : Nat → List Nat
  | 0 => List.range NL
  | i + 1 => (lvAt F NL bs i).filter fun l => F l (bs.getD i 0) == bs.getD i 0

theorem lvAt_sub (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) (i : Nat) :
    ∀ l ∈ lvAt F NL bs i, l < NL := by
  induction i with
  | zero => exact fun l hl => List.mem_range.mp hl
  | succ i ih => exact fun l hl => ih l (List.mem_filter.mp hl).1

@[expose] noncomputable def levMaskAt (n w LT NL : Nat) (bs : List Nat) (i : Nat) : Nat :=
  levLast n w LT NL (bs.take i) (mask NL)

private theorem cg_levLast_append {n w LT NL : Nat} (l₁ l₂ : List Nat) (LV : Nat) :
    levLast n w LT NL (l₁ ++ l₂) LV = levLast n w LT NL l₂ (levLast n w LT NL l₁ LV) := by
  induction l₁ generalizing LV with
  | nil => rfl
  | cons b l₁ ih => exact ih _

private theorem cg_levPairs_gen {n w LT NL : Nat} (bs : List Nat) (LV : Nat) :
    levPairs n w LT NL bs LV = (List.range bs.length).map fun i =>
      (BS.run (letF n w LT) (maskL NL (levLast n w LT NL (bs.take i) LV)) n (bs.getD i 0),
        levLast n w LT NL (bs.take i) LV) := by
  induction bs generalizing LV with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, levPairs, ih]
    rfl

private theorem cg_maskL_levLast_take {n w LT NL : Nat} (bs : List Nat) (i : Nat) :
    maskL NL (levLast n w LT NL (bs.take i) (mask NL)) =
      lvAt (letF n w LT) NL bs (min i bs.length) := by
  induction i with
  | zero =>
    rw [Nat.zero_min]
    exact maskL_mask NL
  | succ i ih =>
    by_cases hi : i < bs.length
    · have h1 : bs.take (i + 1) = bs.take i ++ [bs.getD i 0] := by
        rw [List.take_succ]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have h2 : min (i + 1) bs.length = i + 1 := by omega
      have h3 : min i bs.length = i := by omega
      rw [h3] at ih
      rw [h2, lvAt, ← ih, h1, cg_levLast_append]
      exact maskL_fixMask _ _
    · have h1 : bs.take (i + 1) = bs.take i := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have h2 : min (i + 1) bs.length = min i bs.length := by omega
      rw [h2, ← ih, h1]

theorem levPairs_eq {n w LT NL : Nat} (bs : List Nat) :
    (levPairs n w LT NL bs (mask NL)) = (List.range bs.length).map fun i =>
      (BS.run (letF n w LT) (lvAt (letF n w LT) NL bs i) n (bs.getD i 0),
        levMaskAt n w LT NL bs i) := by
  rw [cg_levPairs_gen]
  apply List.map_congr_left
  intro i hi
  have hi' : i < bs.length := List.mem_range.mp hi
  have h := cg_maskL_levLast_take (n := n) (w := w) (LT := LT) (NL := NL) bs i
  rw [Nat.min_eq_left (Nat.le_of_lt hi')] at h
  show (BS.run (letF n w LT) (maskL NL (levLast n w LT NL (bs.take i) (mask NL))) n
    (bs.getD i 0), levMaskAt n w LT NL bs i) = _
  rw [h]

theorem maskL_levMaskAt {n w LT NL : Nat} (bs : List Nat) (i : Nat) :
    maskL NL (levMaskAt n w LT NL bs i) = lvAt (letF n w LT) NL bs (min i bs.length) :=
  cg_maskL_levLast_take bs i

private theorem cg_getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem cg_getD_lt {bs : List Nat} {n : Nat} (hn : 0 < n) (hbs : ∀ b ∈ bs, b < n)
    (i : Nat) : bs.getD i 0 < n := by
  by_cases hi : i < bs.length
  · exact hbs _ (cg_getD_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact hn

theorem lvAt_congr {F G : Nat → Nat → Nat} {NL n : Nat} {bs : List Nat} (hn : 0 < n)
    (hbs : ∀ b ∈ bs, b < n)
    (h : ∀ l < NL, ∀ x < n, F l x = G l x) (i : Nat) : lvAt F NL bs i = lvAt G NL bs i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (lvAt F NL bs i).filter _ = (lvAt G NL bs i).filter _
    rw [ih]
    apply List.filter_congr
    intro l hl
    rw [h l (lvAt_sub G NL bs i l hl) _ (cg_getD_lt hn hbs i)]

private theorem cg_all_congr {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

private theorem cg_foldl_letter_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n : Nat}
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (h : ∀ l ∈ lv, ∀ x < n, F l x = G l x) {i p : Nat}
    (hp : p < n) :
    ∀ (lv' : List Nat), (∀ l ∈ lv', l ∈ lv) → ∀ (t : BS), (∀ q ∈ t.pts, q < n) →
      lv'.foldl (BS.letter F i p) t = lv'.foldl (BS.letter G i p) t ∧
        ∀ q ∈ (lv'.foldl (BS.letter F i p) t).pts, q < n := by
  intro lv'
  induction lv' with
  | nil => exact fun _ t ht => ⟨rfl, ht⟩
  | cons l lv' ih =>
    intro hsub t ht
    have hl : l ∈ lv := hsub l List.mem_cons_self
    have hsub' : ∀ l' ∈ lv', l' ∈ lv := fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')
    have ht' : ∀ q ∈ (BS.letter F i p t l).pts, q < n := by
      unfold BS.letter
      split
      · exact ht
      · intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact ht q hq
        · rw [List.mem_singleton] at hq
          exact hq ▸ hF l hl p hp
    have hlet : BS.letter F i p t l = BS.letter G i p t l := by
      unfold BS.letter
      rw [h l hl p hp]
    rw [List.foldl_cons, List.foldl_cons, ← hlet]
    exact ih hsub' _ ht'

private theorem cg_step_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n : Nat}
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (h : ∀ l ∈ lv, ∀ x < n, F l x = G l x) {s : BS}
    (hs : ∀ q ∈ s.pts, q < n) (i : Nat) :
    BS.step F lv s i = BS.step G lv s i ∧ ∀ q ∈ (BS.step F lv s i).pts, q < n := by
  unfold BS.step
  by_cases hi : i < s.pts.length
  · rw [if_pos hi, if_pos hi]
    exact cg_foldl_letter_congr hF h (hs _ (cg_getD_mem hi)) lv (fun _ hl => hl) s hs
  · rw [if_neg hi, if_neg hi]
    exact ⟨rfl, hs⟩

private theorem cg_foldl_step_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n : Nat}
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (h : ∀ l ∈ lv, ∀ x < n, F l x = G l x) :
    ∀ (L : List Nat) (s : BS), (∀ q ∈ s.pts, q < n) →
      L.foldl (BS.step F lv) s = L.foldl (BS.step G lv) s := by
  intro L
  induction L with
  | nil => exact fun _ _ => rfl
  | cons i L ih =>
    intro s hs
    obtain ⟨he, hlt⟩ := cg_step_congr hF h hs i
    rw [List.foldl_cons, List.foldl_cons, ← he]
    exact ih _ hlt

theorem run_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n r : Nat} (hr : r < n)
    (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) (h : ∀ l ∈ lv, ∀ x < n, F l x = G l x) :
    BS.run F lv n r = BS.run G lv n r := by
  unfold BS.run
  refine cg_foldl_step_congr hF h _ _ ?_
  intro q hq
  rw [List.mem_singleton] at hq
  exact hq ▸ hr

private theorem cg_trans_pos (F : Nat → Nat → Nat) (s : BS) {k : Nat} (hk0 : 0 < k)
    (hpar : s.par.getD k 0 < k) (x : Nat) :
    BS.trans F s k x = F (s.lab.getD k 0) (BS.trans F s (s.par.getD k 0) x) := by
  rw [BS.trans, dif_pos ⟨hk0, hpar⟩]

private theorem cg_trans_zero (F : Nat → Nat → Nat) (s : BS) (x : Nat) :
    BS.trans F s 0 x = x := by
  rw [BS.trans, dif_neg (by simp)]

private theorem cg_trans_lt {F : Nat → Nat → Nat} {lv : List Nat} {n r : Nat} {s : BS}
    (hs : RunOK n F lv r s) (hF : ∀ l ∈ lv, ∀ x < n, F l x < n) {k : Nat}
    (hk : k < s.pts.length) {x : Nat} (hx : x < n) : BS.trans F s k x < n := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      rw [cg_trans_pos F s hk0 hpar]
      exact hF _ (hs.lab_mem k hk0 hk) _ (ih _ hpar (by omega))
    · have hk0' : k = 0 := by omega
      subst hk0'
      rw [cg_trans_zero]
      exact hx

theorem trans_congr {F G : Nat → Nat → Nat} {lv : List Nat} {n r : Nat} {s : BS}
    (hs : RunOK n F lv r s) (hF : ∀ l ∈ lv, ∀ x < n, F l x < n)
    (h : ∀ l ∈ lv, ∀ x < n, F l x = G l x) {k : Nat} (hk : k < s.pts.length) {x : Nat} (hx : x < n) :
    BS.trans F s k x = BS.trans G s k x := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk0 : 0 < k
    · have hpar := hs.par_lt k hk0 hk
      rw [cg_trans_pos F s hk0 hpar, cg_trans_pos G s hk0 hpar, ← ih _ hpar (by omega)]
      exact h _ (hs.lab_mem k hk0 hk) _ (cg_trans_lt hs hF (by omega) hx)
    · have hk0' : k = 0 := by omega
      subst hk0'
      rw [cg_trans_zero, cg_trans_zero]

@[expose] def LevelOK (n : Nat) (F : Nat → Nat → Nat) (lv : List Nat) (r : Nat) (s : BS) : Prop :=
  RunOK n F lv r s ∧ (∀ l ∈ lv, IsPermN n (F l))

private theorem cg_absSift_congr {F G : Nat → Nat → Nat} {n : Nat} :
    ∀ (L : List (List Nat × Nat × BS)), (∀ e ∈ L, LevelOK n F e.1 e.2.1 e.2.2) →
      (∀ e ∈ L, ∀ l ∈ e.1, ∀ x < n, F l x = G l x) →
      ∀ {g g' : Nat → Nat}, (∀ x < n, g x = g' x) →
        absSift n F (L.map fun e => e.2.2) g = absSift n G (L.map fun e => e.2.2) g' := by
  intro L
  induction L with
  | nil =>
    intro _ _ g g' hgg
    show (List.range n).all (fun x => g x == x) = (List.range n).all (fun x => g' x == x)
    apply cg_all_congr
    intro x hx
    rw [hgg x (List.mem_range.mp hx)]
  | cons e L ih =>
    intro hL h g g' hgg
    have hs : LevelOK n F e.1 e.2.1 e.2.2 := hL e List.mem_cons_self
    have hsh : ∀ l ∈ e.1, ∀ x < n, F l x = G l x := h e List.mem_cons_self
    have hL' : ∀ e' ∈ L, LevelOK n F e'.1 e'.2.1 e'.2.2 := fun e' he' =>
      hL e' (List.mem_cons_of_mem _ he')
    have h' : ∀ e' ∈ L, ∀ l ∈ e'.1, ∀ x < n, F l x = G l x := fun e' he' =>
      h e' (List.mem_cons_of_mem _ he')
    have hFn : ∀ l ∈ e.1, ∀ x < n, F l x < n := fun l hl => (hs.2 l hl).1
    have hroot : g (e.2.2.pts.getD 0 0) = g' (e.2.2.pts.getD 0 0) :=
      hgg _ (hs.1.lt _ (cg_getD_mem hs.1.pos))
    rw [List.map_cons]
    simp only [absSift]
    rw [← hroot]
    by_cases hmem : g (e.2.2.pts.getD 0 0) ∈ e.2.2.pts
    · have hk0 : e.2.2.pts.idxOf (g (e.2.2.pts.getD 0 0)) < e.2.2.pts.length :=
        List.idxOf_lt_length_iff.mpr hmem
      simp only [decide_eq_true hmem, Bool.true_and]
      apply ih hL' h'
      intro x hx
      rw [finv_congr (fun y hy => trans_congr hs.1 hFn hsh hk0 hy), hgg x hx]
    · simp only [decide_eq_false hmem, Bool.false_and]

theorem absSift_congr {F G : Nat → Nat → Nat} {n : Nat} {L : List (List Nat × Nat × BS)}
    (hL : ∀ e ∈ L, LevelOK n F e.1 e.2.1 e.2.2) (h : ∀ e ∈ L, ∀ l ∈ e.1, ∀ x < n, F l x = G l x)
    {g : Nat → Nat} (hg : ∀ x < n, g x < n) :
    absSift n F (L.map fun e => e.2.2) g = absSift n G (L.map fun e => e.2.2) g := by
  clear hg
  exact cg_absSift_congr L hL h fun _ _ => rfl

theorem absSch_congr {F G : Nat → Nat → Nat} {n : Nat} {lv : List Nat} {r : Nat} {s : BS}
    (hs : LevelOK n F lv r s) (hlv : ∀ l ∈ lv, ∀ x < n, F l x = G l x)
    {L : List (List Nat × Nat × BS)}
    (hL : ∀ e ∈ L, LevelOK n F e.1 e.2.1 e.2.2) (h : ∀ e ∈ L, ∀ l ∈ e.1, ∀ x < n, F l x = G l x) :
    absSch n F lv s (L.map fun e => e.2.2) = absSch n G lv s (L.map fun e => e.2.2) := by
  unfold absSch
  apply cg_all_congr
  intro l hl
  apply cg_all_congr
  intro k hk
  have hk' : k < s.pts.length := List.mem_range.mp hk
  have hp : s.pts.getD k 0 < n := hs.1.lt _ (cg_getD_mem hk')
  have hFl : F l (s.pts.getD k 0) = G l (s.pts.getD k 0) := hlv l hl _ hp
  have hFn : ∀ l ∈ lv, ∀ x < n, F l x < n := fun l hl => (hs.2 l hl).1
  rw [← hFl]
  by_cases hmem : F l (s.pts.getD k 0) ∈ s.pts
  · have hk0 : s.pts.idxOf (F l (s.pts.getD k 0)) < s.pts.length :=
      List.idxOf_lt_length_iff.mpr hmem
    simp only [decide_eq_true hmem, Bool.true_and]
    apply cg_absSift_congr L hL h
    intro x hx
    rw [finv_congr (fun y hy => trans_congr hs.1 hFn hlv hk0 hy),
      ← trans_congr hs.1 hFn hlv hk' hx, hlv l hl _ (cg_trans_lt hs.1 hFn hk' hx)]
  · simp only [decide_eq_false hmem, Bool.false_and]

end CFSG.KS.PK

end
