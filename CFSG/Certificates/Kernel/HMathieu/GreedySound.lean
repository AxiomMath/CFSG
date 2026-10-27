module

public import Certificates.Data.Kernel.HMathieu.Greedy
public import CFSG.Quasithin.Background.HMathieuEnumAll

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem all_congr_mem {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

variable {P : Type*} [Group P] [DecidableEq P]

@[expose] def el (R : List P) (k : Nat) : P := R.getD k 1

structure GTabs (R : List P) (cmR mkR : Nat → Nat) : Prop where
  nodup : R.Nodup
  invol : ∀ x ∈ R, x ≠ 1 ∧ x * x = 1
  all : ∀ x : P, x ≠ 1 → x * x = 1 → x ∈ R
  comm : ∀ i < R.length, ∀ j < R.length,
    (cmR i).testBit j = decide (el R i * el R j = el R j * el R i)
  prod : ∀ i < R.length, ∀ j < R.length, el R i * el R j = el R j * el R i →
    mkF mkR R.length i j ≤ R.length ∧ el R (mkF mkR R.length i j) = el R i * el R j

section Pos

variable {R : List P}

theorem el_of_lt {k : Nat} (hk : k < R.length) : el R k = R[k] := by
  simp [el, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem el_of_le {k : Nat} (hk : R.length ≤ k) : el R k = 1 := by
  simp [el, List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

theorem one_notMem {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) : (1 : P) ∉ R :=
  fun h => (T.invol 1 h).1 rfl

theorem idxOf_el {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {k : Nat} (hk : k ≤ R.length) :
    R.idxOf (el R k) = k := by
  rcases Nat.lt_or_ge k R.length with h | h
  · rw [el_of_lt h]
    exact List.Nodup.idxOf_getElem T.nodup k h
  · rw [el_of_le h, List.idxOf_eq_length (one_notMem T)]
    omega

theorem el_idxOf {x : P} (hx : x ∈ R ∨ x = 1) : el R (R.idxOf x) = x := by
  rcases hx with hx | rfl
  · rw [el_of_lt (List.idxOf_lt_length_iff.2 hx), List.getElem_idxOf]
  · by_cases h : (1 : P) ∈ R
    · rw [el_of_lt (List.idxOf_lt_length_iff.2 h), List.getElem_idxOf]
    · rw [el_of_le (by rw [List.idxOf_eq_length h])]

theorem idxOf_le (x : P) : R.idxOf x ≤ R.length := List.idxOf_le_length

theorem idxOf_inj {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {x y : P} (hx : x ∈ R ∨ x = 1)
    (hy : y ∈ R ∨ y = 1) (h : R.idxOf x = R.idxOf y) : x = y := by
  rw [← el_idxOf hx, ← el_idxOf hy, h]

theorem idxOf_eq_length_iff {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {x : P}
    (hx : x ∈ R ∨ x = 1) : R.idxOf x = R.length ↔ x = 1 := by
  constructor
  · intro h
    rcases hx with hx | hx
    · exact absurd h (Nat.ne_of_lt (List.idxOf_lt_length_iff.2 hx))
    · exact hx
  · rintro rfl
    exact List.idxOf_eq_length (one_notMem T)

theorem mem_or_one_of_subprods {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {l : List P}
    (hl : IsCommInvol l) {s : P} (hs : s ∈ subprods l) : s ∈ R ∨ s = 1 := by
  by_cases h1 : s = 1
  · exact Or.inr h1
  · exact Or.inl (T.all s h1 (sq_eq_one_of_mem_subprods hl s hs))

theorem idxOf_mul {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {x s : P} (hx : x ∈ R)
    (hs : s ∈ R ∨ s = 1) (hc : x * s = s * x) :
    R.idxOf (x * s) = mkF mkR R.length (R.idxOf x) (R.idxOf s) := by
  have hxl : R.idxOf x < R.length := List.idxOf_lt_length_iff.2 hx
  rcases hs with hs | rfl
  · have hsl : R.idxOf s < R.length := List.idxOf_lt_length_iff.2 hs
    have hc' : el R (R.idxOf x) * el R (R.idxOf s) = el R (R.idxOf s) * el R (R.idxOf x) := by
      rw [el_idxOf (Or.inl hx), el_idxOf (Or.inl hs)]
      exact hc
    obtain ⟨hle, he⟩ := T.prod _ hxl _ hsl hc'
    rw [el_idxOf (Or.inl hx), el_idxOf (Or.inl hs)] at he
    rw [← he, idxOf_el T hle]
  · rw [mul_one, List.idxOf_eq_length (one_notMem T), mkF, if_neg (Nat.ne_of_lt hxl), if_pos rfl]

end Pos

section Ext

variable {R : List P} {cmR mkR : Nat → Nat}

theorem map_idxOf_drop (hR : R.Nodup) (s : Nat) :
    (R.drop s).map R.idxOf = List.range' s (R.length - s) := by
  have hmap : R.map R.idxOf = List.range R.length := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact List.Nodup.idxOf_getElem hR i (by simpa using h1)
  rw [List.map_drop, hmap, List.range_eq_range', List.drop_range']
  simp

@[expose] def CMask (R : List P) (l : List P) (c : Nat) : Prop :=
  ∀ j < R.length, c.testBit j = l.all fun y => decide (el R j * y = y * el R j)

theorem cmask_nil (R : List P) : CMask R [] (2 ^ R.length - 1) := by
  intro j hj
  simp [Nat.testBit_two_pow_sub_one, hj]

theorem cmask_cons (T : GTabs R cmR mkR) {l : List P} {c : Nat} (hc : CMask R l c) {x : P}
    (hx : x ∈ R) : CMask R (x :: l) (Nat.land c (cmR (R.idxOf x))) := by
  intro j hj
  have hxl : R.idxOf x < R.length := List.idxOf_lt_length_iff.2 hx
  change (c &&& cmR (R.idxOf x)).testBit j = _
  rw [Nat.testBit_and, T.comm _ hxl j hj, el_idxOf (Or.inl hx), hc j hj, List.all_cons,
    Bool.and_comm]
  congr 1
  exact decide_eq_decide.2 eq_comm

theorem cand_eq (T : GTabs R cmR mkR) {l : List P} (hl : IsCommInvol l) {c : Nat}
    (hc : CMask R l c) {x : P} (hx : x ∈ R) :
    ((l.all fun y => decide (x * y = y * x)) && !(decide (x ∈ subprods l)) &&
      ((subprods l).all fun s => decide (s = 1) || decide (R.idxOf x < R.idxOf (x * s)))) =
    (c.testBit (R.idxOf x) && !(((subprods l).map R.idxOf).contains (R.idxOf x)) &&
      ((subprods l).map R.idxOf).all fun s => s == R.length ||
        decide (R.idxOf x < mkF mkR R.length (R.idxOf x) s)) := by
  have hxl : R.idxOf x < R.length := List.idxOf_lt_length_iff.2 hx
  have hS : ∀ s ∈ subprods l, s ∈ R ∨ s = 1 := fun s hs => mem_or_one_of_subprods T hl hs
  have hA : c.testBit (R.idxOf x) = l.all fun y => decide (x * y = y * x) := by
    rw [hc _ hxl, el_idxOf (Or.inl hx)]
  have hB : (((subprods l).map R.idxOf).contains (R.idxOf x)) = decide (x ∈ subprods l) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff, List.mem_map]
    constructor
    · rintro ⟨s, hs, e⟩
      rwa [← idxOf_inj T (hS s hs) (Or.inl hx) e]
    · intro h
      exact ⟨x, h, rfl⟩
  rw [hA, hB]
  cases hall : l.all fun y => decide (x * y = y * x)
  · simp
  · simp only [Bool.true_and]
    congr 1
    rw [List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun s hs => ?_
    have hcomm : x * s = s * x := by
      have hxl' : ∀ y ∈ l, x * y = y * x := by
        intro y hy
        have := List.all_eq_true.1 hall y hy
        simpa using this
      exact commute_subprods hxl' s hs
    have e1 : decide (s = 1) = (R.idxOf s == R.length) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      exact (idxOf_eq_length_iff T (hS s hs)).symm
    simp only [Function.comp_apply]
    rw [e1, idxOf_mul T hx (hS s hs) hcomm]

theorem map_greedyExtP (T : GTabs R cmR mkR) {posF : P → Nat} (hpos : ∀ x, posF x = R.idxOf x)
    {l : List P} (hl : IsCommInvol l) {c : Nat} (hc : CMask R l c) :
    (greedyExtP posF R l).map R.idxOf =
      extK R.length mkR (l.map R.idxOf) ((subprods l).map R.idxOf) c := by
  have key : ∀ s, ((R.drop s).filter fun x =>
      (l.all fun y => decide (x * y = y * x)) && !(decide (x ∈ subprods l)) &&
        ((subprods l).all fun t => decide (t = 1) || decide (posF x < posF (x * t)))).map
          R.idxOf =
      (List.range' s (R.length - s)).filter fun x =>
        c.testBit x && !(((subprods l).map R.idxOf).contains x) &&
          ((subprods l).map R.idxOf).all fun t => t == R.length ||
            decide (x < mkF mkR R.length x t) := by
    intro s
    rw [← map_idxOf_drop T.nodup, List.filter_map]
    congr 1
    refine List.filter_congr fun x hx => ?_
    have hxR : x ∈ R := List.mem_of_mem_drop hx
    simp only [Function.comp_apply, hpos]
    exact cand_eq T hl hc hxR
  unfold greedyExtP extK
  cases l with
  | nil => exact key 0
  | cons a t =>
    have ha : R.idxOf a = posF a := (hpos a).symm
    simp only [List.map_cons, startK, ha]
    exact key (posF a + 1)

theorem mem_greedyExtP {posF : P → Nat} {l : List P} {x : P} (hx : x ∈ greedyExtP posF R l) :
    x ∈ R ∧ (∀ y ∈ l, x * y = y * x) ∧ x ∉ subprods l := by
  unfold greedyExtP at hx
  simp only [List.mem_filter, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hx
  exact ⟨List.mem_of_mem_drop hx.1, hx.2.1.1, hx.2.1.2⟩

theorem map_subprods_cons (T : GTabs R cmR mkR) {x : P} (hx : x ∈ R) {l : List P}
    (hl : IsCommInvol l) (hxl : ∀ y ∈ l, x * y = y * x) :
    (subprods (x :: l)).map R.idxOf = (subprods l).map R.idxOf ++
      ((subprods l).map R.idxOf).map (mkF mkR R.length (R.idxOf x)) := by
  rw [subprods, List.map_append, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  simp only [Function.comp_apply]
  exact idxOf_mul T hx (mem_or_one_of_subprods T hl hs) (commute_subprods hxl s hs)

end Ext

section Search

variable {R : List P} {cmR mkR : Nat → Nat}

theorem forallGreedyAll_eq_gAllS {σ : Type} (T : GTabs R cmR mkR) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (pred : List P → Bool) (upd : σ → Nat → σ)
    (predK : List Nat → List Nat → σ → Bool) (F : List P → σ)
    (hF : ∀ x l, x ∈ R → (∀ y ∈ l, y ∈ R) → IndepList (x :: l) →
      F (x :: l) = upd (F l) (R.idxOf x))
    (hpred : ∀ l, (∀ y ∈ l, y ∈ R) → IndepList l →
      pred l = predK (l.map R.idxOf) ((subprods l).map R.idxOf) (F l)) :
    ∀ k l, (∀ y ∈ l, y ∈ R) → IndepList l → ∀ c, CMask R l c →
      forallGreedyAll posF R pred k l = gAllS R.length cmR mkR upd predK k (l.map R.idxOf)
        ((subprods l).map R.idxOf) c (F l) := by
  intro k
  induction k with
  | zero =>
    intro l hR hl c _
    rw [forallGreedyAll, gAllS, hpred l hR hl]
  | succ k ih =>
    intro l hR hl c hc
    have hci := isCommInvol_of_indepList hl
    rw [forallGreedyAll, gAllS, hpred l hR hl, ← map_greedyExtP T hpos hci hc, List.all_map]
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun x hx => ?_
    obtain ⟨hxR, hxl, hxS⟩ := mem_greedyExtP hx
    have hind : IndepList (x :: l) :=
      IndepList.cons x l (T.invol x hxR).2 (T.invol x hxR).1 hxl hxS hl
    have hR' : ∀ y ∈ x :: l, y ∈ R := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hxR
      · exact hR y hy
    simp only [Function.comp_apply]
    rw [ih (x :: l) hR' hind _ (cmask_cons T hc hxR), List.map_cons,
      map_subprods_cons T hxR hci hxl, hF x l hxR hR hind]

theorem forallGreedyAll_eq_gAllS_nil {σ : Type} (T : GTabs R cmR mkR) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (pred : List P → Bool) (upd : σ → Nat → σ)
    (predK : List Nat → List Nat → σ → Bool) (F : List P → σ)
    (hF : ∀ x l, x ∈ R → (∀ y ∈ l, y ∈ R) → IndepList (x :: l) →
      F (x :: l) = upd (F l) (R.idxOf x))
    (hpred : ∀ l, (∀ y ∈ l, y ∈ R) → IndepList l →
      pred l = predK (l.map R.idxOf) ((subprods l).map R.idxOf) (F l)) (k : Nat) :
    forallGreedyAll posF R pred k [] =
      gAllS R.length cmR mkR upd predK k [] [R.length] (2 ^ R.length - 1) (F []) := by
  rw [forallGreedyAll_eq_gAllS T hpos pred upd predK F hF hpred k [] (by simp) IndepList.nil _
    (cmask_nil R)]
  simp [subprods, List.idxOf_eq_length (one_notMem T)]

end Search

section Raw

theorem lAllR_eq (S : List Nat) (f : Nat → Bool) : lAllR S f = S.all f := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    change bAnd(f s, lAllR S f) = _
    rw [ih, List.all_cons]
    cases f s <;> rfl

theorem appMapR_eq (S T : List Nat) (g : Nat → Nat) : appMapR S T g = S ++ T.map g := by
  have hT : List.rec (motive := fun _ => List Nat) [] (fun t _ ih => g t :: ih) T = T.map g := by
    induction T with
    | nil => rfl
    | cons t T ih => exact congrArg (g t :: ·) ih
  induction S with
  | nil => exact hT
  | cons s S ih => exact congrArg (s :: ·) ih

theorem testBit_eq_beq (c x : Nat) :
    c.testBit x = Nat.beq (Nat.land (Nat.shiftRight c x) 1) 1 := by
  rw [Nat.testBit]
  change (1 &&& c >>> x != 0) = Nat.beq (c >>> x &&& 1) 1
  rw [Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (c >>> x) with h | h <;> rw [h] <;> rfl

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff]
  exact fun e => h (Nat.eq_of_beq_eq_true e)

theorem candR_eq {m : Nat} {mkR : Nat → Nat} {c x : Nat} (hx : x < m) (S : List Nat) :
    candR m c x (mkR x) S = (c.testBit x && !(S.contains x) &&
      S.all fun s => s == m || decide (x < mkF mkR m x s)) := by
  unfold candR
  rw [lAllR_eq, ← testBit_eq_beq]
  cases c.testBit x
  · rfl
  · change S.all _ = _
    simp only [Bool.true_and]
    induction S with
    | nil => rfl
    | cons s S ih =>
      rw [List.all_cons, ih, List.contains_cons, List.all_cons]
      by_cases hs : s = x
      · subst hs
        simp
      · rw [beq_false_of_ne hs]
        have hxs : (x == s) = false := by simpa [beq_iff_eq] using Ne.symm hs
        rw [hxs, Bool.false_or]
        by_cases hm : s = m
        · subst hm
          simp
        · rw [beq_false_of_ne hm]
          have hmF : mkF mkR m x s = Nat.land (Nat.shiftRight (mkR x) (8 * s)) 255 := by
            rw [mkF, if_neg (Nat.ne_of_lt hx), if_neg hm]
          have hb : Nat.blt x (Nat.land (Nat.shiftRight (mkR x) (Nat.mul 8 s)) 255) =
              decide (x < mkF mkR m x s) := by
            rw [hmF, Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
            rfl
          have hsm : (s == m) = false := by simpa [beq_iff_eq] using hm
          change (Nat.blt x _ && _) = _
          rw [hb, hsm, Bool.false_or]
          cases decide (x < mkF mkR m x s) <;>
            cases (List.all S fun s => s == m || decide (x < mkF mkR m x s)) <;>
            cases (List.contains S x) <;> rfl

theorem scan_eq {D : List (Nat × Nat)} {m : Nat} (hD : D.length = m)
    {H : Nat → Nat × Nat → List (Nat × Nat) → Bool} {H' : Nat → Bool}
    (hH : ∀ y < m, H y (D.getD y (0, 0)) (D.drop (y + 1)) = H' y) :
    ∀ x ≤ m, List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun r rest ihs y => bAnd(H y r rest, ihs (Nat.succ y))) (D.drop x) x =
      (List.range' x (m - x)).all H' := by
  have key : ∀ n x, m - x = n → x ≤ m → List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun r rest ihs y => bAnd(H y r rest, ihs (Nat.succ y))) (D.drop x) x =
      (List.range' x (m - x)).all H' := by
    intro n
    induction n with
    | zero =>
      intro x hx _
      have hxm : x = m := by omega
      subst hxm
      rw [List.drop_eq_nil_of_le (by omega), Nat.sub_self]
      rfl
    | succ n ih =>
      intro x hx hxm
      have hxl : x < D.length := by omega
      have e := ih (x + 1) (by omega) (by omega)
      rw [show m - (x + 1) = n by omega] at e
      rw [List.drop_eq_getElem_cons hxl, hx, List.range'_succ, List.all_cons]
      simp only [Nat.succ_eq_add_one]
      rw [e]
      have hg : D[x] = D.getD x (0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxl]
        rfl
      rw [hg, hH x (by omega)]
      cases H' x <;> rfl
  exact fun x hx => key (m - x) x rfl hx

theorem gAllR_eq {σ : Type} {D : List (Nat × Nat)} {m : Nat} (hD : D.length = m)
    (upd : σ → Nat → σ) (pred : List Nat → List Nat → σ → Bool) :
    ∀ k l S c st, startK l ≤ m →
      gAllR m upd pred k l S c st (D.drop (startK l)) (startK l) =
        gAllS m (cmD D) (mkD D) upd pred k l S c st := by
  intro k
  induction k with
  | zero => intro l S c st _; rfl
  | succ k ih =>
    intro l S c st hl
    change bAnd(pred l S st, List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun r rest ihs y => bAnd(bIf(candR m c y r.2 S,
        gAllR m upd pred k (y :: l) (appMapR S S fun s => nIf(Nat.beq s m, y,
          Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st y) rest
          (Nat.succ y), true), ihs (Nat.succ y))) (D.drop (startK l)) (startK l)) = _
    rw [scan_eq hD (H' := fun y => !(candR m c y (mkD D y) S) ||
        gAllS m (cmD D) (mkD D) upd pred k (y :: l) (S ++ S.map (mkF (mkD D) m y))
          (Nat.land c (cmD D y)) (upd st y)) ?_ _ hl]
    · rw [gAllS, extK, List.all_filter]
      cases pred l S st
      · rfl
      · change (List.range' _ _).all _ = (List.range' _ _).all _
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        refine forall₂_congr fun y hy => ?_
        have hym : y < m := by
          rw [List.mem_range'_1] at hy
          omega
        rw [candR_eq hym]
    · intro y hy
      have hgy : mkD D y = (D.getD y (0, 0)).2 := rfl
      have hcy : cmD D y = (D.getD y (0, 0)).1 := rfl
      change bIf(candR m c y (D.getD y (0, 0)).2 S, gAllR m upd pred k (y :: l) _ _ _ _ _,
        true) = _
      have e := ih (y :: l) (appMapR S S fun s => nIf(Nat.beq s m, y,
          Nat.land (Nat.shiftRight (D.getD y (0, 0)).2 (Nat.mul 8 s)) 255))
        (Nat.land c (D.getD y (0, 0)).1) (upd st y) (by simp only [startK]; omega)
      simp only [startK] at e
      rw [e, ← hgy, ← hcy, appMapR_eq]
      have hmap : (S.map fun s => nIf(Nat.beq s m, y,
          Nat.land (Nat.shiftRight (mkD D y) (Nat.mul 8 s)) 255)) = S.map (mkF (mkD D) m y) := by
        refine List.map_congr_left fun s _ => ?_
        rw [mkF, if_neg (Nat.ne_of_lt hy)]
        by_cases hs : s = m
        · subst hs
          rw [if_pos rfl, Nat.beq_refl]
        · rw [if_neg hs, beq_false_of_ne hs]
          rfl
      rw [hmap]
      cases candR m c y (mkD D y) S <;> rfl

end Raw

end CFSG.KC.HMathieu

end
