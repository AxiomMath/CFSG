module

public import Certificates.Data.Kernel.J4Pent
public import CFSG.Certificates.Kernel.J4Q.Rep

public section

namespace CFSG.KC.J4Pent

open CFSG.KC.Loop CFSG.KC.J4Q

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem nthL_eq {α : Type} (d : α) (l : List α) (i : Nat) : nthL d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem dropK_eq {α : Type} (n : Nat) (l : List α) : dropK n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x t => exact ih t

theorem takeK_eq {α : Type} (n : Nat) (l : List α) : takeK n l = l.take n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons x t => exact congrArg (List.cons x) (ih t)

theorem mapS_eq (f : Nat → Nat) (l : List Nat) : mapS f l = l.map f := by
  induction l with
  | nil => rfl
  | cons x t ih => exact congrArg (List.cons (f x)) ih

theorem zipS_eq (f : Nat → Nat → Nat) (A B : List Nat) : zipS f A B = List.zipWith f A B := by
  induction A generalizing B with
  | nil => rfl
  | cons a t ih =>
    cases B with
    | nil => rfl
    | cons b bs => exact congrArg (List.cons (f a b)) (ih bs)

theorem eqL_iff (A B : List Nat) : eqL A B = true ↔ A = B := by
  induction A generalizing B with
  | nil => cases B <;> simp [eqL]
  | cons a t ih =>
    cases B with
    | nil => simp [eqL]
    | cons b bs =>
      change bAnd(Nat.beq a b, eqL t bs) = true ↔ _
      simp only [bAnd_eq, Bool.and_eq_true, ih bs, List.cons.injEq, Nat.beq_eq]

theorem allB_eq {α : Type} (p : α → Bool) (l : List α) : allB p l = l.all p := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change bAnd(p x, allB p t) = _
    rw [bAnd_eq, ih, List.all_cons]

theorem anyB_eq {α : Type} (p : α → Bool) (l : List α) : anyB p l = l.any p := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change bIf(p x, true, anyB p t) = _
    rw [bIf_eq, ih, List.any_cons]
    cases p x <;> rfl

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change strictN (lenK t) (fun n => Nat.succ n) = _
    rw [strictN_eq, ih, List.length_cons]

theorem appendK_eq {α : Type} (L L' : List α) : appendK L L' = L ++ L' := by
  induction L with
  | nil => rfl
  | cons x t ih => exact congrArg (List.cons x) ih

theorem allLt_iff (b n : Nat) (l : List Nat) :
    allLt b n l = true ↔ l.length = n ∧ ∀ x ∈ l, x < b := by
  induction l generalizing n with
  | nil =>
    change Nat.beq n 0 = true ↔ _
    rw [Nat.beq_eq, List.length_nil]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -⟩
      exact h.symm
  | cons x t ih =>
    change bAnd(Nat.blt x b, Nat.rec (motive := fun _ => Bool) false (fun m _ => allLt b m t) n) =
      true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq]
    cases n with
    | zero => simp
    | succ m =>
      change x < b ∧ allLt b m t = true ↔ _
      rw [ih m]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
      tauto

theorem bitK_eq (c k : Nat) : bitK c k = c.testBit k := by
  change Nat.beq ((c >>> k) &&& 1) 1 = _
  rw [and_one_bit]
  cases c.testBit k <;> rfl

theorem testBit_one_succ (n : Nat) : Nat.testBit 1 (n + 1) = false := by
  rw [Nat.testBit_succ]
  simp

theorem testBit_maskOf (L : List Nat) (l : Nat) : (maskOf L).testBit l = decide (l ∈ L) := by
  induction L with
  | nil => simp [maskOf]
  | cons x t ih =>
    change (strictN (maskOf t) fun r => Nat.lor r (Nat.shiftLeft 1 x)).testBit l = _
    rw [strictN_eq]
    change (maskOf t ||| 1 <<< x).testBit l = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : l = x
    · subst h
      simp
    · simp [h, Ne.symm h]

noncomputable def laneVF (B : List Nat) (l j0 : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih j => strictN (ih (Nat.succ j)) fun r =>
      Nat.lor r (Nat.shiftLeft (Nat.land (Nat.shiftRight b l) 1) j)) B j0

theorem testBit_laneVF (B : List Nat) (l : Nat) : ∀ j0 j,
    (laneVF B l j0).testBit j = (decide (j0 ≤ j) && (B.getD (j - j0) 0).testBit l) := by
  induction B with
  | nil => intro j0 j; simp [laneVF]
  | cons b t ih =>
    intro j0 j
    change (strictN (laneVF t l (j0 + 1)) fun r =>
      Nat.lor r (Nat.shiftLeft (Nat.land (Nat.shiftRight b l) 1) j0)).testBit j = _
    rw [strictN_eq]
    change (laneVF t l (j0 + 1) ||| ((b >>> l) &&& 1) <<< j0).testBit j = _
    rw [Nat.testBit_or, ih, and_one_bit, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy j j0 with h | rfl | h
    · simp [show ¬ j0 + 1 ≤ j by omega, show ¬ j0 ≤ j by omega]
    · cases hb : b.testBit l <;> simp [hb]
    · have e : j - j0 = (j - (j0 + 1)) + 1 := by omega
      rw [e]
      cases hb : b.testBit l <;>
        simp [hb, show j0 + 1 ≤ j by omega, show j0 ≤ j by omega, testBit_one_succ]

theorem testBit_laneV (B : List Nat) (l j : Nat) :
    (laneV B l).testBit j = (B.getD j 0).testBit l := by
  have e : laneV B l = laneVF B l 0 := rfl
  rw [e, testBit_laneVF]
  simp

theorem laneV_lt (B : List Nat) (l : Nat) : laneV B l < 2 ^ B.length := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_laneV, List.getD_eq_default _ _ hj, Nat.zero_testBit]

theorem nxor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nlor (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nland (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nshl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem nshr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nmul (a b : Nat) : Nat.mul a b = a * b := rfl

@[expose] noncomputable def xsel (c b0 b1 b2 b3 : Nat) : Nat :=
  (if c.testBit 0 then b0 else 0) ^^^ (if c.testBit 1 then b1 else 0) ^^^
    (if c.testBit 2 then b2 else 0) ^^^ (if c.testBit 3 then b3 else 0)

theorem selT_tr4 (b0 b1 b2 b3 c : Nat) : selT (tr4 b0 b1 b2 b3) c = xsel c b0 b1 b2 b3 := by
  unfold selT tr4 xsel
  simp only [bitK_eq, nxor]
  cases c.testBit 0 <;> cases c.testBit 1 <;> cases c.testBit 2 <;> cases c.testBit 3 <;>
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.zero_testBit, Bool.false_eq_true, ite_false, ite_true]
    generalize b0.testBit i = p0
    generalize b1.testBit i = p1
    generalize b2.testBit i = p2
    generalize b3.testBit i = p3
    revert p0 p1 p2 p3
    decide

theorem tb_blk {x W i : Nat} (hx : x < 2 ^ W) (hi : i < W) (k e : Nat) :
    (x <<< (k * W)).testBit (e * W + i) = (decide (k = e) && x.testBit i) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy k e with h | rfl | h
  · have h1 : k * W + W ≤ e * W := by
      have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      exact this
    have h2 : W ≤ e * W + i - k * W := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h2))]
    simp [Nat.ne_of_lt h]
  · simp
  · have h1 : e * W + W ≤ k * W := by
      have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      exact this
    simp [show ¬ e * W + i ≥ k * W by omega, Nat.ne_of_gt h]

theorem tb_blk0 {x W i : Nat} (hx : x < 2 ^ W) (hi : i < W) (e : Nat) :
    x.testBit (e * W + i) = (decide (0 = e) && x.testBit i) := by
  have h := tb_blk hx hi 0 e
  rwa [Nat.zero_mul, Nat.shiftLeft_zero] at h

theorem tb_blk1 {x W i : Nat} (hx : x < 2 ^ W) (hi : i < W) (e : Nat) :
    (x <<< W).testBit (e * W + i) = (decide (1 = e) && x.testBit i) := by
  have h := tb_blk hx hi 1 e
  rwa [Nat.one_mul] at h

theorem xsel_lt {W : Nat} {b0 b1 b2 b3 : Nat} (h0 : b0 < 2 ^ W) (h1 : b1 < 2 ^ W) (h2 : b2 < 2 ^ W)
    (h3 : b3 < 2 ^ W) (c : Nat) : xsel c b0 b1 b2 b3 < 2 ^ W := by
  have z : (0 : Nat) < 2 ^ W := Nat.two_pow_pos W
  unfold xsel
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_ <;> split <;> assumption

theorem xsel_and15 (c b0 b1 b2 b3 : Nat) : xsel (c &&& 15) b0 b1 b2 b3 = xsel c b0 b1 b2 b3 := by
  have e : ∀ k < 4, (c &&& 15).testBit k = c.testBit k := by
    intro k hk
    rw [Nat.testBit_and, show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hk]
  unfold xsel
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]

theorem entry_tab4 {W : Nat} {b0 b1 b2 b3 : Nat} (h0 : b0 < 2 ^ W) (h1 : b1 < 2 ^ W)
    (h2 : b2 < 2 ^ W) (h3 : b3 < 2 ^ W) (c : Nat) :
    (tab4 W b0 b1 b2 b3 >>> ((c &&& 15) * W)) &&& (2 ^ W - 1) = xsel c b0 b1 b2 b3 := by
  rw [← xsel_and15]
  have he : c &&& 15 < 16 := Nat.lt_succ_of_le (Nat.and_le_right)
  generalize c &&& 15 = e at he ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < W
  · rw [decide_eq_true hi, Bool.and_true]
    unfold tab4
    simp only [nxor, nlor, nshl, nmul]
    rw [Nat.testBit_shiftLeft]
    rcases e with _ | e
    · simp only [Nat.zero_mul, Nat.zero_add, ge_iff_le, show ¬ W ≤ i by omega, decide_false,
        Bool.false_and]
      unfold xsel
      simp
    · have ee : (e + 1) * W + i - W = e * W + i := by rw [Nat.succ_mul]; omega
      rw [ee, decide_eq_true (by rw [Nat.succ_mul]; omega), Bool.true_and]
      simp only [Nat.testBit_or]
      simp (disch := ((repeat' apply Nat.xor_lt_two_pow) <;> assumption)) only
        [tb_blk (hi := hi), tb_blk1 h1 hi, tb_blk0 h0 hi]
      unfold xsel
      have he' : e < 15 := by omega
      interval_cases e <;>
        simp (config := {decide := true}) only [Nat.testBit_xor, Nat.zero_testBit, Bool.true_and,
          Bool.false_and, Bool.or_false, Bool.false_or, ↓reduceIte, Nat.reduceAdd] <;>
        (generalize b0.testBit i = p0
         generalize b1.testBit i = p1
         generalize b2.testBit i = p2
         generalize b3.testBit i = p3
         revert p0 p1 p2 p3
         decide)
  · rw [decide_eq_false hi, Bool.and_false,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (xsel_lt h0 h1 h2 h3 e)
        (Nat.pow_le_pow_right (by omega) (by omega)))]

@[expose] def bsum (g : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bsum g n ^^ g n

theorem testBit_xsum (f : Nat → Nat) (l : Nat) :
    ∀ n, (xsum f n).testBit l = bsum (fun k => (f k).testBit l) n
  | 0 => by
    change Nat.testBit 0 l = false
    exact Nat.zero_testBit l
  | n + 1 => by
    rw [xsum_succ, Nat.testBit_xor, testBit_xsum f l n]
    rfl

theorem bsum_congr {g h : Nat → Bool} : ∀ {n : Nat}, (∀ k < n, g k = h k) → bsum g n = bsum h n
  | 0, _ => rfl
  | n + 1, H => by
    change (bsum g n ^^ g n) = (bsum h n ^^ h n)
    rw [bsum_congr (fun k hk => H k (by omega)), H n (by omega)]

theorem bsum_false {g : Nat → Bool} : ∀ {n : Nat}, (∀ k < n, g k = false) → bsum g n = false
  | 0, _ => rfl
  | n + 1, H => by
    change (bsum g n ^^ g n) = false
    rw [bsum_false (fun k hk => H k (by omega)), H n (by omega)]
    rfl

theorem getD_drop (l : List Nat) (n m : Nat) : (l.drop n).getD m 0 = l.getD (n + m) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_range_map (f : Nat → Nat) (n j : Nat) :
    ((List.range n).map f).getD j 0 = if j < n then f j else 0 := by
  by_cases h : j < n
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]

@[expose] noncomputable def selS (B : List Nat) (c n : Nat) : Nat :=
  xsum (fun i => if c.testBit i then B.getD i 0 else 0) n

theorem testBit_selS (B : List Nat) (c n l : Nat) :
    (selS B c n).testBit l = bsum (fun i => c.testBit i && (B.getD i 0).testBit l) n := by
  unfold selS
  rw [testBit_xsum]
  refine bsum_congr fun k _ => ?_
  cases c.testBit k <;> simp

theorem selS_four (B : List Nat) (c n : Nat) :
    selS B c (4 * (n + 1)) =
      xsel c (B.getD 0 0) (B.getD 1 0) (B.getD 2 0) (B.getD 3 0) ^^^ selS (B.drop 4) (c >>> 4) (4 * n) := by
  unfold selS
  rw [show 4 * (n + 1) = 4 + 4 * n by ring, xsum_add]
  congr 1
  · change (((0 ^^^ _) ^^^ _) ^^^ _) ^^^ _ = _
    rw [Nat.zero_xor]
    rfl
  · refine xsum_congr fun k _ => ?_
    rw [Nat.testBit_shiftRight, getD_drop]

noncomputable def dotWF (W ones : Nat) (Ts : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun T _ ih c acc => strictN acc fun a =>
      ih (Nat.shiftRight c 4)
        (Nat.xor a (Nat.land (Nat.shiftRight T (Nat.mul (Nat.land c 15) W)) ones)))
    Ts

theorem dotWF_tabsW {W : Nat} : ∀ (n : Nat) (B : List Nat), (∀ i, B.getD i 0 < 2 ^ W) →
    ∀ c acc, dotWF W (2 ^ W - 1) (tabsW W B n) c acc = acc ^^^ selS B c (4 * n)
  | 0, B, _, c, acc => by
    change acc = acc ^^^ 0
    rw [Nat.xor_zero]
  | n + 1, B, hB, c, acc => by
    change (strictN acc fun a => dotWF W (2 ^ W - 1) (tabsW W (dropK 4 B) n) (Nat.shiftRight c 4)
      (Nat.xor a (Nat.land (Nat.shiftRight (tab4 W (nthL 0 B 0) (nthL 0 B 1) (nthL 0 B 2)
        (nthL 0 B 3)) (Nat.mul (Nat.land c 15) W)) (2 ^ W - 1)))) = _
    rw [strictN_eq, dotWF_tabsW n _ (fun i => by rw [dropK_eq, getD_drop]; exact hB _),
      dropK_eq, nthL_eq, nthL_eq, nthL_eq, nthL_eq]
    simp only [nxor, nland, nshr, nmul]
    rw [entry_tab4 (hB 0) (hB 1) (hB 2) (hB 3), selS_four, Nat.xor_assoc]

theorem dotW_tabsW {W : Nat} {B : List Nat} (hB : ∀ x ∈ B, x < 2 ^ W) (c : Nat) :
    dotW W (2 ^ W - 1) (tabsW W B 28) c = selS B c 112 := by
  have hB' : ∀ i, B.getD i 0 < 2 ^ W := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : B[i]? with
    | none => exact Nat.two_pow_pos W
    | some x => exact hB x (List.mem_of_getElem? h)
  have h := dotWF_tabsW 28 B hB' c 0
  rw [Nat.zero_xor] at h
  exact h

noncomputable def dotTF (Ts : List T16) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun T _ ih c acc => strictN acc fun a => ih (Nat.shiftRight c 4) (Nat.xor a (selT T c)))
    Ts

theorem dotTF_tabsT : ∀ (n : Nat) (B : List Nat) (c acc : Nat),
    dotTF (tabsT B n) c acc = acc ^^^ selS B c (4 * n)
  | 0, B, c, acc => by
    change acc = acc ^^^ 0
    rw [Nat.xor_zero]
  | n + 1, B, c, acc => by
    change (strictN acc fun a => dotTF (tabsT (dropK 4 B) n) (Nat.shiftRight c 4)
      (Nat.xor a (selT (tr4 (nthL 0 B 0) (nthL 0 B 1) (nthL 0 B 2) (nthL 0 B 3)) c))) = _
    rw [strictN_eq, dotTF_tabsT n, dropK_eq, nthL_eq, nthL_eq, nthL_eq, nthL_eq, selT_tr4]
    simp only [nxor, nshr]
    rw [selS_four, Nat.xor_assoc]

theorem dotT_tabsT (B : List Nat) (c : Nat) : dotT (tabsT B 28) c = selS B c 112 := by
  have h := dotTF_tabsT 28 B c 0
  rw [Nat.zero_xor] at h
  exact h

theorem rm_lit : (nat_lit 5192296858534827628530496329220095) = 2 ^ 112 - 1 := by decide

theorem appW_eq (W ones MT : Nat) (Ts : List Nat) : ∀ n lo, appW W ones MT Ts lo n =
    (List.range n).map (fun j => dotW W ones Ts (rowJ (2 ^ 112 - 1) MT (lo + j)))
  | 0, _ => rfl
  | n + 1, lo => by
    change dotW W ones Ts (rowJ (nat_lit 5192296858534827628530496329220095) MT lo) ::
      appW W ones MT Ts (lo + 1) n = _
    rw [appW_eq W ones MT Ts n (lo + 1), List.range_succ_eq_map, List.map_cons, List.map_map,
      rm_lit, Nat.add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show lo + 1 + j = lo + (j + 1) by omega]

theorem appT_eq (MT : Nat) (Ts : List T16) : ∀ n lo, appT MT Ts lo n =
    (List.range n).map (fun j => dotT Ts (rowJ (2 ^ 112 - 1) MT (lo + j)))
  | 0, _ => rfl
  | n + 1, lo => by
    change dotT Ts (rowJ (nat_lit 5192296858534827628530496329220095) MT lo) ::
      appT MT Ts (lo + 1) n = _
    rw [appT_eq MT Ts n (lo + 1), List.range_succ_eq_map, List.map_cons, List.map_map,
      rm_lit, Nat.add_zero]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show lo + 1 + j = lo + (j + 1) by omega]

theorem testBit_vecJ (rm x m j : Nat) :
    (vecJ rm x m).testBit j = bsum (fun k => x.testBit k && (rowJ rm m k).testBit j) 112 := by
  rw [vecJ_eq, testBit_xsum]
  refine bsum_congr fun k _ => ?_
  rw [and_one_bit]
  cases x.testBit k <;> simp

@[expose] def IsTr (MT M : Nat) : Prop :=
  ∀ i < 112, ∀ j < 112, (rowJ (2 ^ 112 - 1) MT j).testBit i = (rowJ (2 ^ 112 - 1) M i).testBit j

theorem bsum_sel_tr {MT M : Nat} (hT : IsTr MT M) (B : List Nat) {j : Nat} (hj : j < 112) (l : Nat) :
    bsum (fun i => (rowJ (2 ^ 112 - 1) MT j).testBit i && (B.getD i 0).testBit l) 112 =
      (vecJ (2 ^ 112 - 1) (laneV B l) M).testBit j := by
  rw [testBit_vecJ]
  refine bsum_congr fun k hk => ?_
  rw [hT k hk j hj, testBit_laneV, Bool.and_comm]

theorem testBit_vecJ_ge (x m : Nat) {j : Nat} (hj : 112 ≤ j) :
    (vecJ (2 ^ 112 - 1) x m).testBit j = false := by
  rw [testBit_vecJ]
  refine bsum_false fun k _ => ?_
  have : (rowJ (2 ^ 112 - 1) m k).testBit j = false := by
    change ((m >>> (k * 128)) &&& (2 ^ 112 - 1)).testBit j = false
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [show ¬ j < 112 by omega]
  rw [this, Bool.and_false]

theorem testBit_laneV_appW {W MT M : Nat} (hT : IsTr MT M) {B : List Nat}
    (hB : ∀ x ∈ B, x < 2 ^ W) (lo n l j : Nat) (hn : lo + n ≤ 112) :
    (laneV (appW W (2 ^ W - 1) MT (tabsW W B 28) lo n) l).testBit j =
      (decide (j < n) && (vecJ (2 ^ 112 - 1) (laneV B l) M).testBit (lo + j)) := by
  rw [testBit_laneV, appW_eq, getD_range_map]
  by_cases hj : j < n
  · rw [if_pos hj, dotW_tabsW hB, testBit_selS, bsum_sel_tr hT B (by omega)]
    simp [hj]
  · rw [if_neg hj]
    simp [hj]

theorem laneV_appT {MT M : Nat} (hT : IsTr MT M) (B : List Nat) (l : Nat) :
    laneV (appT MT (tabsT B 28) 0 112) l = vecJ (2 ^ 112 - 1) (laneV B l) M := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_laneV, appT_eq, getD_range_map, Nat.zero_add]
  by_cases hj : j < 112
  · rw [if_pos hj, dotT_tabsT, testBit_selS, bsum_sel_tr hT B hj]
  · rw [if_neg hj, Nat.zero_testBit, testBit_vecJ_ge _ _ (by omega : 112 ≤ j)]

theorem length_appT (MT : Nat) (Ts : List T16) (n lo : Nat) : (appT MT Ts lo n).length = n := by
  rw [appT_eq, List.length_map, List.length_range]

theorem length_appW (W ones MT : Nat) (Ts : List Nat) (n lo : Nat) :
    (appW W ones MT Ts lo n).length = n := by
  rw [appW_eq, List.length_map, List.length_range]

theorem laneV_nil (l : Nat) : laneV [] l = 0 := rfl

theorem laneV_cons (x : Nat) (xs : List Nat) (l : Nat) :
    laneV (x :: xs) l = (if x.testBit l then 1 else 0) + 2 * laneV xs l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_laneV]
  cases j with
  | zero =>
    rw [Nat.testBit_zero, List.getD_cons_zero]
    cases h : x.testBit l
    · rw [if_neg (by simp)]
      simp
    · rw [if_pos rfl]
      simp
  | succ j =>
    rw [Nat.testBit_succ, List.getD_cons_succ, ← testBit_laneV]
    congr 1
    cases x.testBit l <;> simp <;> omega

theorem lex_lt (u w : Nat) (x y : Bool) :
    ((if x = true then 1 else 0) + 2 * u < (if y = true then 1 else 0) + 2 * w) ↔
      (u < w ∨ (u = w ∧ x = false ∧ y = true)) := by
  cases x <;> cases y <;> simp <;> constructor <;> intro h <;> omega

theorem lex_eq (u w : Nat) (x y : Bool) :
    ((if x = true then 1 else 0) + 2 * u = (if y = true then 1 else 0) + 2 * w) ↔
      (u = w ∧ x = y) := by
  cases x <;> cases y <;> simp <;> omega

theorem cmpS_cons (ones a b : Nat) (as bs : List Nat) : cmpS ones (a :: as) (b :: bs) =
    ((cmpS ones as bs).1 ||| ((cmpS ones as bs).2 &&& ((a ^^^ ones) &&& b)),
      (cmpS ones as bs).2 &&& ((a ^^^ b) ^^^ ones)) := rfl

theorem cmpS_spec (ones : Nat) : ∀ (A B : List Nat), A.length = B.length → ∀ l,
    (cmpS ones A B).1.testBit l = (ones.testBit l && decide (laneV A l < laneV B l)) ∧
    (cmpS ones A B).2.testBit l = (ones.testBit l && decide (laneV A l = laneV B l))
  | [], [], _, l => by
    refine ⟨?_, ?_⟩
    · change Nat.testBit 0 l = _
      simp [laneV_nil]
    · change ones.testBit l = _
      simp [laneV_nil]
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: as, b :: bs, h, l => by
    obtain ⟨h1, h2⟩ := cmpS_spec ones as bs (by simpa using h) l
    rw [cmpS_cons, laneV_cons, laneV_cons]
    generalize cmpS ones as bs = r at h1 h2 ⊢
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2]
    generalize laneV as l = u at ⊢
    generalize laneV bs l = w at ⊢
    simp only [lex_lt, lex_eq]
    cases ones.testBit l <;> cases a.testBit l <;> cases b.testBit l <;> simp

theorem incrS_spec {N : Nat} {R : List Nat} (h : incrS (2 ^ N - 1) R = true) :
    ∀ l, l + 1 < N → laneV R l < laneV R (l + 1) := by
  intro l hl
  have e : incrS (2 ^ N - 1) R = Nat.beq ((cmpS (2 ^ N - 1) R (mapS (fun x => Nat.shiftRight x 1) R)).1
      &&& ((2 ^ N - 1) >>> 1)) ((2 ^ N - 1) >>> 1) := rfl
  rw [e, Nat.beq_eq] at h
  have hb := congrArg (fun x => x.testBit l) h
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at hb
  have hm : decide (1 + l < N) = true := by simp; omega
  rw [hm, Bool.and_true] at hb
  have hlen : R.length = (mapS (fun x => Nat.shiftRight x 1) R).length := by
    rw [mapS_eq, List.length_map]
  rw [(cmpS_spec _ R _ hlen l).1, Nat.testBit_two_pow_sub_one] at hb
  have hsh : laneV (mapS (fun x => Nat.shiftRight x 1) R) l = laneV R (l + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_laneV, testBit_laneV, mapS_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases R[j]? with
    | none => simp
    | some x =>
      change (x >>> 1).testBit l = x.testBit (l + 1)
      rw [Nat.testBit_shiftRight, Nat.add_comm]
  rw [hsh] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.2

theorem canonAt_spec {W ones n MT tie : Nat} {Ts Rt : List Nat}
    (h : canonAt W ones n Ts Rt MT tie = true) :
    ((cmpS ones Rt (appW W ones MT Ts (112 - n) n)).1 |||
        (cmpS ones Rt (appW W ones MT Ts (112 - n) n)).2) = ones ∧
      (cmpS ones Rt (appW W ones MT Ts (112 - n) n)).2 = tie := by
  have e : canonAt W ones n Ts Rt MT tie =
      bAnd(Nat.beq ((cmpS ones Rt (appW W ones MT Ts (112 - n) n)).1 |||
        (cmpS ones Rt (appW W ones MT Ts (112 - n) n)).2) ones,
        Nat.beq (cmpS ones Rt (appW W ones MT Ts (112 - n) n)).2 tie) := rfl
  rw [e, bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  exact h

theorem getD_map0 {f : Nat → Nat} (hf : f 0 = 0) (l : List Nat) (j : Nat) :
    (l.map f).getD j 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[j]? with
  | none => exact hf.symm
  | some x => rfl

theorem getD_zipWith0 {f : Nat → Nat → Nat} (hf : f 0 0 = 0) :
    ∀ (A B : List Nat), A.length = B.length → ∀ j,
      (List.zipWith f A B).getD j 0 = f (A.getD j 0) (B.getD j 0)
  | [], [], _, j => by simp [hf]
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: as, b :: bs, h, j => by
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.zipWith_cons_cons, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      exact getD_zipWith0 hf as bs (by simpa using h) j

@[expose] noncomputable def stepV (MA MB MC mA mB mC l v : Nat) : Nat :=
  if mA.testBit l then vecJ (2 ^ 112 - 1) v MA else
    if mB.testBit l then vecJ (2 ^ 112 - 1) v MB else
      if mC.testBit l then vecJ (2 ^ 112 - 1) v MC else v

@[expose] noncomputable def walkV (MA MB MC : Nat) (S : List (Nat × Nat × Nat)) (l v : Nat) : Nat :=
  S.foldl (fun v s => stepV MA MB MC s.1 s.2.1 s.2.2 l v) v

@[expose] def Disj (s : Nat × Nat × Nat) : Prop :=
  s.1 &&& s.2.1 = 0 ∧ s.1 &&& s.2.2 = 0 ∧ s.2.1 &&& s.2.2 = 0

theorem length_stepT (ones AT BT CT mA mB mC : Nat) {Y : List Nat} (hY : Y.length = 112) :
    (stepT ones AT BT CT mA mB mC Y).length = 112 := by
  unfold stepT
  simp only [zipS_eq, mapS_eq, List.length_zipWith, List.length_map, length_appT, hY]
  rfl

theorem laneV_stepT {N AT BT CT MA MB MC : Nat} (hA : IsTr AT MA) (hB : IsTr BT MB)
    (hC : IsTr CT MC) {mA mB mC : Nat} (hd : Disj (mA, mB, mC)) {Y : List Nat}
    (hY : Y.length = 112) {l : Nat} (hl : l < N) :
    laneV (stepT (2 ^ N - 1) AT BT CT mA mB mC Y) l = stepV MA MB MC mA mB mC l (laneV Y l) := by
  obtain ⟨d1, d2, d3⟩ := hd
  have hd1 := congrArg (fun x => x.testBit l) d1
  have hd2 := congrArg (fun x => x.testBit l) d2
  have hd3 := congrArg (fun x => x.testBit l) d3
  simp only [Nat.testBit_and, Nat.zero_testBit] at hd1 hd2 hd3
  have eA := laneV_appT hA Y l
  have eB := laneV_appT hB Y l
  have eC := laneV_appT hC Y l
  have lA := length_appT AT (tabsT Y 28) 112 0
  have lB := length_appT BT (tabsT Y 28) 112 0
  have lC := length_appT CT (tabsT Y 28) 112 0
  unfold stepT stepV
  simp only [zipS_eq, mapS_eq]
  generalize appT AT (tabsT Y 28) 0 112 = PA at eA lA ⊢
  generalize appT BT (tabsT Y 28) 0 112 = PB at eB lB ⊢
  generalize appT CT (tabsT Y 28) 0 112 = PC at eC lC ⊢
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_laneV, getD_zipWith0 (by simp [nlor, nland]) _ _
      (by simp [hY, lA, lB, lC]),
    getD_zipWith0 (by simp [nlor, nland]) _ _ (by simp [lA, lB, lC]),
    getD_zipWith0 (by simp [nlor, nland]) _ _ (by simp [lA, lB]),
    getD_map0 (by simp [nland])]
  simp only [nlor, nland, nxor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one, decide_eq_true hl, Bool.true_xor]
  have tA : (PA.getD j 0).testBit l = (vecJ (2 ^ 112 - 1) (laneV Y l) MA).testBit j := by
    rw [← eA, testBit_laneV]
  have tB : (PB.getD j 0).testBit l = (vecJ (2 ^ 112 - 1) (laneV Y l) MB).testBit j := by
    rw [← eB, testBit_laneV]
  have tC : (PC.getD j 0).testBit l = (vecJ (2 ^ 112 - 1) (laneV Y l) MC).testBit j := by
    rw [← eC, testBit_laneV]
  rw [tA, tB, tC, ← testBit_laneV Y l j]
  cases ha : mA.testBit l <;> cases hb : mB.testBit l <;> cases hc : mC.testBit l <;>
    simp_all

theorem walkT_cons (ones AT BT CT : Nat) (s : Nat × Nat × Nat) (S : List (Nat × Nat × Nat))
    (Y : List Nat) : walkT ones AT BT CT (s :: S) Y =
      walkT ones AT BT CT S (stepT ones AT BT CT s.1 s.2.1 s.2.2 Y) := rfl

theorem laneV_walkT {N AT BT CT MA MB MC : Nat} (hA : IsTr AT MA) (hB : IsTr BT MB)
    (hC : IsTr CT MC) {l : Nat} (hl : l < N) :
    ∀ (S : List (Nat × Nat × Nat)), (∀ s ∈ S, Disj s) → ∀ (Y : List Nat), Y.length = 112 →
      (walkT (2 ^ N - 1) AT BT CT S Y).length = 112 ∧
        laneV (walkT (2 ^ N - 1) AT BT CT S Y) l = walkV MA MB MC S l (laneV Y l)
  | [], _, Y, hY => ⟨hY, rfl⟩
  | s :: S, hS, Y, hY => by
    rw [walkT_cons]
    have h1 := laneV_walkT hA hB hC hl S (fun t ht => hS t (List.mem_cons_of_mem _ ht))
      (stepT (2 ^ N - 1) AT BT CT s.1 s.2.1 s.2.2 Y) (length_stepT _ _ _ _ _ _ _ hY)
    refine ⟨h1.1, ?_⟩
    rw [h1.2, laneV_stepT hA hB hC (hS s (List.mem_cons_self ..)) hY hl]
    rfl

theorem mapT_eq (M : Nat) (L : List (List Nat)) :
    List.rec (motive := fun _ => List (List Nat)) List.nil
      (fun X _ ih => List.cons (appT M (tabsT X 28) 0 112) ih) L =
      L.map (fun X => appT M (tabsT X 28) 0 112) := by
  induction L with
  | nil => rfl
  | cons X t ih => exact congrArg (List.cons _) ih

theorem subsT_succ (Ms : List Nat) (j0 k : Nat) (Y : List Nat) :
    subsT Ms j0 (k + 1) Y = subsT Ms j0 k Y ++
      (subsT Ms j0 k Y).map (fun X => appT (Ms.getD (j0 + k) 0) (tabsT X 28) 0 112) := by
  change appendK (subsT Ms j0 k Y) (List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun X _ ih => List.cons (appT (nthL 0 Ms (Nat.add j0 k)) (tabsT X 28) 0 112) ih)
    (subsT Ms j0 k Y)) = _
  rw [appendK_eq, mapT_eq, nthL_eq]
  rfl

@[expose] noncomputable def prodV (Mf : Nat → Nat) (j0 a : Nat) : Nat → Nat → Nat
  | 0, v => v
  | k + 1, v => if a.testBit k then vecJ (2 ^ 112 - 1) (prodV Mf j0 a k v) (Mf (j0 + k))
      else prodV Mf j0 a k v

theorem prodV_succ (Mf : Nat → Nat) (j0 a k v : Nat) : prodV Mf j0 a (k + 1) v =
    if a.testBit k then vecJ (2 ^ 112 - 1) (prodV Mf j0 a k v) (Mf (j0 + k))
      else prodV Mf j0 a k v := rfl

theorem prodV_congr (Mf : Nat → Nat) (j0 : Nat) {a b : Nat} :
    ∀ k, (∀ i < k, a.testBit i = b.testBit i) → ∀ v, prodV Mf j0 a k v = prodV Mf j0 b k v
  | 0, _, _ => rfl
  | k + 1, h, v => by
    unfold prodV
    rw [prodV_congr Mf j0 k (fun i hi => h i (by omega)) v, h k (by omega)]

theorem subsT_spec {Ms : List Nat} {Mf : Nat → Nat} {j0 : Nat} {Y : List Nat}
    (hY : Y.length = 112) : ∀ k, (∀ i < k, IsTr (Ms.getD (j0 + i) 0) (Mf (j0 + i))) →
      (subsT Ms j0 k Y).length = 2 ^ k ∧ ∀ a < 2 ^ k,
        ((subsT Ms j0 k Y).getD a []).length = 112 ∧
          ∀ L, laneV ((subsT Ms j0 k Y).getD a []) L = prodV Mf j0 a k (laneV Y L)
  | 0, _ => by
    refine ⟨rfl, fun a ha => ?_⟩
    have : a = 0 := by omega
    subst this
    exact ⟨hY, fun L => rfl⟩
  | k + 1, hT => by
    obtain ⟨hlen, hent⟩ := subsT_spec hY k (fun i hi => hT i (by omega))
    rw [subsT_succ]
    refine ⟨by rw [List.length_append, List.length_map, hlen, Nat.pow_succ]; omega, ?_⟩
    intro a ha
    by_cases hak : a < 2 ^ k
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hak)]
      refine ⟨(hent a hak).1, fun L => ?_⟩
      rw [(hent a hak).2 L, prodV_succ]
      rw [if_neg (by rw [Nat.testBit_lt_two_pow hak]; simp)]
    · have hb : a - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at ha; omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
        List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by rw [hlen]; exact hb), Option.map_some, Option.getD_some,
        ← List.getD_eq_getElem _ [] (by rw [hlen]; exact hb)]
      refine ⟨length_appT _ _ _ _, fun L => ?_⟩
      rw [laneV_appT (hT k (by omega)), (hent _ hb).2 L, prodV_succ]
      have ea : a = 2 ^ k + (a - 2 ^ k) := by omega
      rw [if_pos (by rw [ea, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb]; rfl)]
      congr 1
      refine prodV_congr Mf j0 k (fun i hi => ?_) _
      rw [ea, Nat.testBit_two_pow_add_gt hi, Nat.add_sub_cancel_left]

noncomputable def orX (A : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih B => List.rec (motive := fun _ => Nat) 0
      (fun b bs _ => strictN (ih bs) fun r => Nat.lor r (Nat.xor a b)) B) A

theorem orX_false {p : Nat} : ∀ (A B : List Nat),
    (∀ j < A.length, (A.getD j 0).testBit p = (B.getD j 0).testBit p) → (orX A B).testBit p = false
  | [], _, _ => Nat.zero_testBit p
  | _ :: _, [], _ => Nat.zero_testBit p
  | a :: as, b :: bs, h => by
    change (strictN (orX as bs) fun r => Nat.lor r (Nat.xor a b)).testBit p = false
    rw [strictN_eq, nlor, nxor, Nat.testBit_or, Nat.testBit_xor,
      orX_false as bs (fun j hj => by simpa using h (j + 1) (by simp; omega))]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    rw [h0]
    simp

theorem agree4_of {W h l : Nat} (hl : l < W) {A B : List Nat}
    (hAB : ∀ j < h, ∀ k < 4, (A.getD j 0).testBit (l + k * W) = (B.getD j 0).testBit (l + k * W)) :
    (agree4 W (2 ^ W - 1) (2 ^ (4 * W) - 1) h A B).testBit l = true := by
  have hX : ∀ k < 4, (orX (takeK h A) B).testBit (l + k * W) = false := by
    intro k hk
    refine orX_false _ _ fun j hj => ?_
    rw [takeK_eq] at hj ⊢
    rw [List.length_take] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega),
      ← List.getD_eq_getElem?_getD]
    exact hAB j (by omega) k hk
  have he : ∀ k < 4, ((2 ^ (4 * W) - 1) ^^^ orX (takeK h A) B).testBit (l + k * W) = true := by
    intro k hk
    rw [Nat.testBit_xor, hX k hk, Nat.testBit_two_pow_sub_one]
    have : l + k * W < 4 * W := by
      have := Nat.mul_le_mul_right W (show k ≤ 3 by omega)
      omega
    simp [this]
  change ((2 ^ W - 1) &&& ((((2 ^ (4 * W) - 1) ^^^ orX (takeK h A) B) &&&
    (((2 ^ (4 * W) - 1) ^^^ orX (takeK h A) B) >>> W)) &&&
    ((((2 ^ (4 * W) - 1) ^^^ orX (takeK h A) B) >>> (2 * W)) &&&
      (((2 ^ (4 * W) - 1) ^^^ orX (takeK h A) B) >>> (3 * W))))).testBit l = true
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  have h3 := he 3 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h0 h1
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true hl, Bool.true_and]
  rw [h0, show W + l = l + W by omega, h1, show 2 * W + l = l + 2 * W by omega, h2,
    show 3 * W + l = l + 3 * W by omega, h3]
  rfl

noncomputable def innerR (W one1 ones4 h : Nat) (A : List Nat) (Bs : List (List Nat)) (r : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) r
    (fun B _ ih2 => strictN ih2 fun r2 => Nat.lor r2 (agree4 W one1 ones4 h A B)) Bs

theorem innerR_cons (W one1 ones4 h : Nat) (A B : List Nat) (Bs : List (List Nat)) (r : Nat) :
    innerR W one1 ones4 h A (B :: Bs) r =
      innerR W one1 ones4 h A Bs r ||| agree4 W one1 ones4 h A B := by
  change strictN (innerR W one1 ones4 h A Bs r) (fun r2 => Nat.lor r2 (agree4 W one1 ones4 h A B))
    = _
  rw [strictN_eq]
  rfl

theorem innerR_mono {W one1 ones4 h l : Nat} (A : List Nat) {r : Nat} (hr : r.testBit l = true) :
    ∀ Bs, (innerR W one1 ones4 h A Bs r).testBit l = true
  | [] => hr
  | B :: Bs => by
    rw [innerR_cons, Nat.testBit_or, innerR_mono A hr Bs, Bool.true_or]

theorem innerR_mem {W one1 ones4 h l : Nat} (A : List Nat) {B : List Nat}
    (hB : (agree4 W one1 ones4 h A B).testBit l = true) (r : Nat) :
    ∀ Bs, B ∈ Bs → (innerR W one1 ones4 h A Bs r).testBit l = true
  | [], hm => absurd hm (List.not_mem_nil)
  | B' :: Bs, hm => by
    rw [innerR_cons, Nat.testBit_or]
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [hB, Bool.or_true]
    · rw [innerR_mem A hB r Bs hm, Bool.true_or]

theorem anyAgree_cons (W one1 ones4 h : Nat) (A : List Nat) (As Bs : List (List Nat)) :
    anyAgree W one1 ones4 h (A :: As) Bs =
      innerR W one1 ones4 h A Bs (anyAgree W one1 ones4 h As Bs) := by
  change strictN (anyAgree W one1 ones4 h As Bs) (fun r => innerR W one1 ones4 h A Bs r) = _
  rw [strictN_eq]

theorem anyAgree_of {W one1 ones4 h l : Nat} {A B : List Nat}
    (hAB : (agree4 W one1 ones4 h A B).testBit l = true) {Bs : List (List Nat)} (hB : B ∈ Bs) :
    ∀ As, A ∈ As → (anyAgree W one1 ones4 h As Bs).testBit l = true
  | [], hm => absurd hm (List.not_mem_nil)
  | A' :: As, hm => by
    rw [anyAgree_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · exact innerR_mem _ hAB _ Bs hB
    · exact innerR_mono _ (anyAgree_of hAB hB As hm) Bs

theorem getD_mem {α : Type} {l : List α} {a : Nat} (d : α) (h : a < l.length) : l.getD a d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem getD_drop1 {α : Type} (l : List α) {a : Nat} (d : α) (h : 1 ≤ a) :
    l.getD a d = (l.drop 1).getD (a - 1) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

theorem pairFlags_of {W one1 ones4 h l : Nat} {As Bs : List (List Nat)} {a b : Nat}
    (ha : a < As.length) (hb : b < Bs.length) (hab : a ≠ 0 ∨ b ≠ 0)
    (hag : (agree4 W one1 ones4 h (As.getD a []) (Bs.getD b [])).testBit l = true) :
    (pairFlags W one1 ones4 h As Bs).testBit l = true := by
  change (anyAgree W one1 ones4 h (takeK 1 As) (dropK 1 Bs) |||
    anyAgree W one1 ones4 h (dropK 1 As) Bs).testBit l = true
  rw [Nat.testBit_or, takeK_eq, dropK_eq, dropK_eq]
  by_cases h0 : a = 0
  · subst h0
    have hb1 : 1 ≤ b := by omega
    rw [getD_drop1 Bs [] hb1] at hag
    have hA : As.getD 0 [] ∈ As.take 1 := by
      cases As with
      | nil => simp at ha
      | cons A0 rest => simp
    rw [anyAgree_of hag (getD_mem _ (by simp; omega)) _ hA, Bool.true_or]
  · rw [getD_drop1 As [] (by omega)] at hag
    rw [anyAgree_of hag (getD_mem _ hb) _ (getD_mem _ (by simp; omega)), Bool.or_true]

end CFSG.KC.J4Pent

end
