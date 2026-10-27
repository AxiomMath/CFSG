module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34QBridge
public import Certificates.Data.Kernel.L34Q.Defs
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat

public section

namespace CFSG.Quasithin.H13.Ch9.L34Q.KS

open CFSG.Fischer CFSG.Quasithin
open CFSG.KC.Misc (letN)
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.Misc.Spec (xsum foldF2 stepF2 mulF2_eq_fold testBit_stepF2 shl1_eq)
open CFSG.KC.L34Q (fm actN matN IDQ BP plane kerMask xlate spanAdd imMask letRec invRecsK subB
  memL countK popK capStepB plusStepB allR capOKK plusOKK eqRecs)

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem letRec_eq (y : ℕ) (k : ℕ → List (ℕ × (ℕ × ℕ))) : letRec y k = k y := by
  cases y <;> rfl

theorem brec_and (x b : Bool) : (Bool.rec (motive := fun _ => Bool) false x b) = (b && x) := by
  cases b <;> rfl

theorem brec_or (x b : Bool) : (Bool.rec (motive := fun _ => Bool) x true b) = (b || x) := by
  cases b <;> rfl

theorem brec_imp (x b : Bool) :
    (Bool.rec (motive := fun _ => Bool) true x b) = (!b || x) := by
  cases b <;> rfl

theorem pow_lt_256 {k : ℕ} (hk : k < 8) : 2 ^ k < 256 := by
  interval_cases k <;> norm_num

theorem pow_le_256 {k : ℕ} (hk : k ≤ 8) : 2 ^ k ≤ 256 := by
  interval_cases k <;> norm_num

theorem lt_256_two_pow {x : ℕ} (hx : x < 256) : x < 2 ^ 8 := by norm_num; exact hx

theorem xor_lt_256 {x y : ℕ} (hx : x < 256) (hy : y < 256) : x ^^^ y < 256 :=
  Nat.xor_lt_two_pow (n := 8) (lt_256_two_pow hx) (lt_256_two_pow hy)

theorem blt_and (w j : ℕ) : Nat.blt 0 (Nat.land w (Nat.shiftLeft 1 j)) = w.testBit j := by
  rw [shl1_eq]
  have h : Nat.land w (2 ^ j) = if w.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (w &&& 2 ^ j).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hij : j = i
    · subst hij
      cases hw : w.testBit j <;> simp [hw]
    · cases hw : w.testBit j <;> simp [hij]
  rw [h]
  cases hw : w.testBit j
  · rfl
  · simp only [↓reduceIte]
    rw [Nat.blt_eq]
    exact Nat.two_pow_pos j

theorem xor_eq_zero_iff {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl
    exact Nat.xor_self a

theorem xsum_congr {f h : ℕ → Bool} : ∀ n, (∀ k < n, f k = h k) → xsum f n = xsum h n
  | 0, _ => rfl
  | n + 1, hk => by
    rw [xsum, xsum, xsum_congr n fun k hk' => hk k (by omega), hk n (by omega)]

theorem memL_mem {x : ℕ} : ∀ {l : List ℕ}, memL x l = true → x ∈ l
  | [], h => (Bool.false_ne_true h).elim
  | z :: l, h => by
    change Bool.rec (motive := fun _ => Bool) (memL x l) true (Nat.beq x z) = true at h
    rw [brec_or, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with h | h
    · subst h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (memL_mem h)

theorem subB_iff {a b : ℕ} : subB a b = true ↔ a &&& b = a := by
  unfold subB
  rw [Nat.beq_eq]
  rfl

theorem allR_mem {R : List ℕ} {f : ℕ → Bool} : allR R f = true → ∀ W ∈ R, f W = true := by
  induction R with
  | nil => intro _ W hW; simp at hW
  | cons W0 R ih =>
    intro h W hW
    change Bool.rec (motive := fun _ => Bool) false (allR R f) (f W0) = true at h
    rw [brec_and, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hW with rfl | hW
    · exact h.1
    · exact ih h.2 W hW

theorem eqRecs_eq : ∀ (a b : List (ℕ × (ℕ × ℕ))), eqRecs a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => (Bool.false_ne_true h).elim
  | _ :: _, [] => fun h => (Bool.false_ne_true h).elim
  | (L, (fx, cm)) :: a, (L', (fx', cm')) :: b => fun h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (eqRecs a b) (Nat.beq cm cm'))
      (Nat.beq fx fx')) (Nat.beq L L') = true at h
    simp only [brec_and, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    rw [eqRecs_eq a b h]

theorem countK_eq (D : List (ℕ × (ℕ × ℕ))) (W : ℕ) :
    countK D W = D.countP (fun d => subB W d.2.1 && subB d.2.2 W) := by
  induction D with
  | nil => rfl
  | cons d D ih =>
    obtain ⟨L, fx, cm⟩ := d
    change letN (countK D W) (fun c => Bool.rec (motive := fun _ => ℕ) c (Nat.succ c)
      (Bool.rec (motive := fun _ => Bool) false (subB cm W) (subB W fx))) = _
    simp only [letN_eq, ih, List.countP_cons, brec_and]
    cases subB W fx <;> cases subB cm W <;> rfl

theorem popK_aux (W : ℕ) : ∀ n, (Nat.rec (motive := fun _ => ℕ) 0 (fun v ih => letN ih fun c =>
    Nat.add c (Nat.land (Nat.shiftRight W v) 1)) n : ℕ) =
      (List.range n).countP fun v => W.testBit v
  | 0 => rfl
  | n + 1 => by
    have e : Nat.land (Nat.shiftRight W n) 1 = if W.testBit n then 1 else 0 := by
      have e1 : Nat.land (Nat.shiftRight W n) 1 = (W >>> n) % 2 := Nat.and_one_is_mod _
      rw [e1, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (W / 2 ^ n) with h | h <;> simp [h]
    change letN _ _ = _
    rw [letN_eq, popK_aux W n]
    beta_reduce
    rw [e, List.range_succ, List.countP_append, List.countP_singleton]
    rfl

theorem popK_eq (W : ℕ) : popK W = popcount W := by
  unfold popK popcount
  exact popK_aux W 256

theorem fm_code (x y : F4) : fm x.code.val y.code.val = (x * y).code.val := by
  revert x y
  decide +kernel

theorem land_three (n : ℕ) : Nat.land n 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2

theorem shiftRight_div (n k : ℕ) : Nat.shiftRight n k = n / 2 ^ k := Nat.shiftRight_eq_div_pow n k

theorem code_lanes (X : M2) :
    Nat.land (code X) 3 = (X 0 0).code.val ∧
    Nat.land (Nat.shiftRight (code X) 2) 3 = (X 0 1).code.val ∧
    Nat.land (Nat.shiftRight (code X) 4) 3 = (X 1 0).code.val ∧
    Nat.shiftRight (code X) 6 = (X 1 1).code.val := by
  have h1 := (X 0 0).code.isLt
  have h2 := (X 0 1).code.isLt
  have h3 := (X 1 0).code.isLt
  have h4 := (X 1 1).code.isLt
  simp only [land_three, shiftRight_div]
  unfold code
  omega

theorem actN_code (a a' b1 b b2 : F4) (s t : Bool) (X : M2) :
    actN a.code.val a'.code.val b1.code.val b.code.val b2.code.val s.toNat t.toNat (code X) =
      code (gmap !![1, a; 0, a'] !![b1, b; 0, b2] s t X) := by
  obtain ⟨l1, l2, l3, l4⟩ := code_lanes X
  unfold actN
  simp only [letN_eq, l1, l2, l3, l4]
  have hb0 : Nat.beq 0 1 = false := rfl
  have hb1 : Nat.beq 1 1 = true := rfl
  cases s <;> cases t <;>
  simp only [Bool.toNat_true, Bool.toNat_false, hb0, hb1, gmap, frob, code, Bool.false_eq_true,
    ↓reduceIte, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, zero_mul, mul_zero,
    zero_add, add_zero, code_val_add, ← fm_code] <;>
  rfl

theorem act_mk (a a' b1 b b2 : F4) (s t : Bool) {v : ℕ} (hv : v < 256) :
    act ⟨!![1, a; 0, a'], !![b1, b; 0, b2], s, t⟩ v =
      actN a.code.val a'.code.val b1.code.val b.code.val b2.code.val s.toNat t.toNat v := by
  unfold act
  conv_rhs => rw [← code_decode hv]
  rw [actN_code]

@[expose] noncomputable def actP (p : Par) (v : ℕ) : ℕ :=
  actN (p.A 0 1).code.val (p.A 1 1).code.val (p.B 0 0).code.val (p.B 0 1).code.val
    (p.B 1 1).code.val p.s.toNat p.t.toNat v

@[expose] noncomputable def matP (p : Par) : ℕ :=
  matN (p.A 0 1).code.val (p.A 1 1).code.val (p.B 0 0).code.val (p.B 0 1).code.val
    (p.B 1 1).code.val p.s.toNat p.t.toNat

theorem params_shape {p : Par} (hp : p ∈ params) : ∃ a a' b1 b b2 : F4, ∃ s t : Bool,
    a' ∈ nzF4 ∧ b1 ∈ nzF4 ∧ b2 ∈ nzF4 ∧ p = ⟨!![1, a; 0, a'], !![b1, b; 0, b2], s, t⟩ := by
  unfold params at hp
  simp only [List.mem_flatMap, List.mem_map] at hp
  obtain ⟨a, -, a', ha', b1, hb1, b, -, b2, hb2, s, -, t, -, rfl⟩ := hp
  exact ⟨a, a', b1, b, b2, s, t, ha', hb1, hb2, rfl⟩

theorem act_eq_actP {p : Par} (hp : p ∈ params) {v : ℕ} (hv : v < 256) : act p v = actP p v := by
  obtain ⟨a, a', b1, b, b2, s, t, -, -, -, rfl⟩ := params_shape hp
  rw [act_mk _ _ _ _ _ _ _ hv]
  rfl

theorem code_zero : code (0 : M2) = 0 := rfl

theorem act_xor {g : MulAut VM4} {p : Par} (hg : Realizes g p) {u w : ℕ} (hu : u < 256)
    (hw : w < 256) : act p (u ^^^ w) = act p u ^^^ act p w := by
  rw [act_eq_of_realizes hg, act_eq_of_realizes hg, act_eq_of_realizes hg, decode_xor hu hw,
    ofAdd_add, map_mul, toAdd_mul, code_add]

theorem act_zero {g : MulAut VM4} {p : Par} (hg : Realizes g p) : act p 0 = 0 := by
  rw [act_eq_of_realizes hg, decode_zero, ofAdd_zero, map_one, toAdd_one, code_zero]

theorem act_lt (p : Par) (v : ℕ) : act p v < 256 := code_lt _

def xs (f : ℕ → ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xs f v n ^^^ (if v.testBit n then f (2 ^ n) else 0)

theorem testBit_xs (f : ℕ → ℕ) (v i : ℕ) : ∀ n,
    (xs f v n).testBit i = xsum (fun k => v.testBit k && (f (2 ^ k)).testBit i) n
  | 0 => by simp [xs, xsum]
  | n + 1 => by
    rw [xs, xsum, Nat.testBit_xor, testBit_xs f v i n]
    cases v.testBit n <;> simp

theorem xs_congr {f h : ℕ → ℕ} (v : ℕ) : ∀ n, (∀ k < n, f (2 ^ k) = h (2 ^ k)) →
    xs f v n = xs h v n
  | 0, _ => rfl
  | n + 1, hk => by
    rw [xs, xs, xs_congr v n fun k hk' => hk k (by omega), hk n (by omega)]

theorem xs_lin {f : ℕ → ℕ} (hf : ∀ u < 256, ∀ w < 256, f (u ^^^ w) = f u ^^^ f w) (h0 : f 0 = 0)
    (v : ℕ) : ∀ n, n ≤ 8 → f (v % 2 ^ n) = xs f v n
  | 0, _ => by simp [xs, Nat.mod_one, h0]
  | n + 1, hn => by
    have hlt : v % 2 ^ n < 256 :=
      lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n)) (pow_le_256 (by omega))
    have hlt2 : (if v.testBit n then 2 ^ n else 0) < 256 := by
      split
      · exact pow_lt_256 (by omega)
      · norm_num
    rw [mod_two_pow_succ_eq, hf _ hlt _ hlt2, xs_lin hf h0 v n (by omega), xs]
    split <;> simp [h0]

theorem xor4 (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

@[expose] def cmp (p : Par) (v : ℕ) : ℕ := act p v ^^^ v

theorem cmp_lt (p : Par) {v : ℕ} (hv : v < 256) : cmp p v < 256 := xor_lt_256 (act_lt p v) hv

theorem act_eq_xs {g : MulAut VM4} {p : Par} (hg : Realizes g p) {v : ℕ} (hv : v < 256) :
    act p v = xs (act p) v 8 := by
  rw [← xs_lin (fun u hu w hw => act_xor hg hu hw) (act_zero hg) v 8 le_rfl,
    Nat.mod_eq_of_lt (by norm_num; exact hv)]

theorem cmp_eq_xs {g : MulAut VM4} {p : Par} (hg : Realizes g p) {v : ℕ} (hv : v < 256) :
    cmp p v = xs (cmp p) v 8 := by
  have hf : ∀ u < 256, ∀ w < 256, cmp p (u ^^^ w) = cmp p u ^^^ cmp p w := by
    intro u hu w hw
    unfold cmp
    rw [act_xor hg hu hw, xor4]
  have h0 : cmp p 0 = 0 := by
    unfold cmp
    rw [act_zero hg]
    rfl
  rw [← xs_lin hf h0 v 8 le_rfl, Nat.mod_eq_of_lt (by norm_num; exact hv)]

theorem xs_lt {f : ℕ → ℕ} (v : ℕ) : ∀ n, n ≤ 8 → (∀ k < n, f (2 ^ k) < 256) → xs f v n < 256
  | 0, _, _ => by norm_num [xs]
  | n + 1, hn, hf => by
    rw [xs]
    refine xor_lt_256 (xs_lt v n (by omega) fun k hk => hf k (by omega)) ?_
    split
    · exact hf n (by omega)
    · norm_num

theorem testBit_pack (f : ℕ → ℕ) : ∀ m, (∀ k < m, f k < 256) → ∀ k i, i < 8 →
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun k ih => Nat.lor ih (Nat.shiftLeft (f k) (Nat.mul 8 k))) m : ℕ).testBit (8 * k + i) =
      (decide (k < m) && (f k).testBit i)
  | 0, _, k, i, _ => by simp
  | m + 1, hf, k, i, hi => by
    change (_ ||| (f m <<< (8 * m))).testBit (8 * k + i) = _
    rw [Nat.testBit_or, testBit_pack f m (fun k hk => hf k (by omega)) k i hi,
      Nat.testBit_shiftLeft]
    rcases lt_trichotomy k m with h | rfl | h
    · have : ¬ (8 * k + i ≥ 8 * m) := by omega
      simp [h, Nat.lt_succ_of_lt h, this]
    · simp
    · have h1 : ¬ k < m := by omega
      have h2 : ¬ k < m + 1 := by omega
      have h3 : (f m).testBit (8 * k + i - 8 * m) = false := by
        apply Nat.testBit_lt_two_pow
        calc f m < 256 := hf m (by omega)
          _ = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (8 * k + i - 8 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp [h1, h2, h3]

theorem testBit_matP {p : Par} (hp : p ∈ params) {k i : ℕ} (hk : k < 8) (hi : i < 8) :
    (matP p).testBit (8 * k + i) = (act p (2 ^ k)).testBit i := by
  have hf : ∀ k < 8, actP p (Nat.shiftLeft 1 k) < 256 := by
    intro k hk
    rw [shl1_eq, ← act_eq_actP hp (pow_lt_256 hk)]
    exact act_lt p _
  have h := testBit_pack (fun k => actP p (Nat.shiftLeft 1 k)) 8 hf k i hi
  beta_reduce at h
  change (Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => Nat.lor ih
    (Nat.shiftLeft (actP p (Nat.shiftLeft 1 k)) (Nat.mul 8 k))) 8 : ℕ).testBit (8 * k + i) = _
  rw [h, shl1_eq, ← act_eq_actP hp (pow_lt_256 hk)]
  simp [hk]

theorem IDQ_bit : ∀ k < 8, ∀ i < 8, IDQ.testBit (8 * k + i) = decide (k = i) := by
  decide +kernel

theorem IDQ_lt : IDQ < 2 ^ 64 := by
  unfold IDQ
  norm_num

@[expose] noncomputable def recL (p : Par) : ℕ := matP p ^^^ IDQ

theorem testBit_recL {p : Par} (hp : p ∈ params) {k i : ℕ} (hk : k < 8) (hi : i < 8) :
    (recL p).testBit (8 * k + i) = (cmp p (2 ^ k)).testBit i := by
  unfold recL cmp
  rw [Nat.testBit_xor, testBit_matP hp hk hi, IDQ_bit k hk i hi, Nat.testBit_xor,
    Nat.testBit_two_pow]

theorem lane_recL {p : Par} (hp : p ∈ params) {k : ℕ} (hk : k < 8) :
    Nat.land (Nat.shiftRight (recL p) (Nat.mul 8 k)) 255 = cmp p (2 ^ k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((recL p >>> (8 * k)) &&& (2 ^ 8 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 8
  · rw [testBit_recL hp hk hi]
    simp [hi]
  · have : (cmp p (2 ^ k)).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc cmp p (2 ^ k) < 256 := cmp_lt p (pow_lt_256 hk)
        _ = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hi, this]

theorem testBit_foldF2' (A B : ℕ) {i j : ℕ} (hj : j < 8) : ∀ m,
    (foldF2 8 A B m).testBit (8 * i + j) =
      (decide (i < 8) && xsum (fun k => A.testBit (8 * i + k) && B.testBit (8 * k + j)) m)
  | 0 => by simp [foldF2, xsum]
  | m + 1 => by
    rw [foldF2, Nat.testBit_xor, testBit_foldF2' A B hj m, testBit_stepF2 (by norm_num) A B m hj,
      xsum]
    cases decide (i < 8) <;> simp

theorem mulF2_eq_IDQ {M : ℕ}
    (h : ∀ i < 8, ∀ j < 8,
      xsum (fun k => M.testBit (8 * i + k) && M.testBit (8 * k + j)) 8 = decide (i = j)) :
    mulF2 8 M M = IDQ := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hj : q % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hq : q = 8 * (q / 8) + q % 8 := (Nat.div_add_mod q 8).symm
  rw [hq, mulF2_eq_fold (by norm_num), testBit_foldF2' M M hj 8]
  rcases lt_or_ge (q / 8) 8 with hi | hi
  · rw [h _ hi _ hj, IDQ_bit _ hi _ hj]
    simp [hi]
  · have : IDQ.testBit (8 * (q / 8) + q % 8) = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le IDQ_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]
    simp [Nat.not_lt.mpr hi]

theorem mulF2_matP {g : MulAut VM4} {p : Par} (hp : p ∈ params) (hg : Realizes g p)
    (h2 : g * g = 1) : mulF2 8 (matP p) (matP p) = IDQ := by
  have hinv := isInvAct_of_realizes hg h2
  unfold isInvAct at hinv
  rw [List.all_eq_true] at hinv
  apply mulF2_eq_IDQ
  intro i hi j hj
  have e : xsum (fun k => (matP p).testBit (8 * i + k) && (matP p).testBit (8 * k + j)) 8 =
      xsum (fun k => (act p (2 ^ i)).testBit k && (act p (2 ^ k)).testBit j) 8 :=
    xsum_congr 8 fun k hk => by rw [testBit_matP hp hi hk, testBit_matP hp hk hj]
  rw [e, ← testBit_xs (act p) (act p (2 ^ i)) j 8, ← act_eq_xs hg (act_lt p _)]
  have := hinv i (List.mem_range.mpr hi)
  rw [beq_iff_eq] at this
  rw [this, Nat.testBit_two_pow]

theorem BP_bit : ∀ k < 8, ∀ v < 256, (BP.getD k 0).testBit v = v.testBit k := by
  decide +kernel

theorem BP_lt : ∀ k < 8, BP.getD k 0 < 2 ^ 256 := by
  decide +kernel

theorem brecN_bit (B v : ℕ) (b : Bool) :
    (Bool.rec (motive := fun _ => ℕ) 0 B b : ℕ).testBit v = (b && B.testBit v) := by
  cases b <;> simp

theorem brecN_lt {B : ℕ} (hB : B < 2 ^ 256) (b : Bool) :
    (Bool.rec (motive := fun _ => ℕ) 0 B b : ℕ) < 2 ^ 256 := by
  cases b
  · exact Nat.two_pow_pos _
  · exact hB

@[expose] noncomputable def pt (L i k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (BP.getD k 0)
    (Nat.blt 0 (Nat.land L (Nat.shiftLeft 1 (Nat.add (Nat.mul 8 k) i))))

theorem plane_eq (L i : ℕ) : plane L i = pt L i 0 ^^^ (pt L i 1 ^^^ (pt L i 2 ^^^
    (pt L i 3 ^^^ (pt L i 4 ^^^ (pt L i 5 ^^^ (pt L i 6 ^^^ (pt L i 7 ^^^ 0))))))) := rfl

theorem pt_bit (L i : ℕ) {k : ℕ} (hk : k < 8) {v : ℕ} (hv : v < 256) :
    (pt L i k).testBit v = (L.testBit (8 * k + i) && v.testBit k) := by
  unfold pt
  rw [brecN_bit, blt_and, BP_bit k hk v hv]
  rfl

theorem pt_lt (L i : ℕ) {k : ℕ} (hk : k < 8) : pt L i k < 2 ^ 256 :=
  brecN_lt (BP_lt k hk) _

theorem plane_lt (L i : ℕ) : plane L i < 2 ^ 256 := by
  rw [plane_eq]
  repeat' apply Nat.xor_lt_two_pow
  all_goals first
    | exact pt_lt L i (by norm_num)
    | exact Nat.two_pow_pos _

theorem plane_bit_gen (L i : ℕ) {v : ℕ} (hv : v < 256) :
    (plane L i).testBit v = xsum (fun k => L.testBit (8 * k + i) && v.testBit k) 8 := by
  rw [plane_eq]
  simp only [Nat.testBit_xor, Nat.zero_testBit, pt_bit L i (by norm_num : (0 : ℕ) < 8) hv,
    pt_bit L i (by norm_num : (1 : ℕ) < 8) hv, pt_bit L i (by norm_num : (2 : ℕ) < 8) hv,
    pt_bit L i (by norm_num : (3 : ℕ) < 8) hv, pt_bit L i (by norm_num : (4 : ℕ) < 8) hv,
    pt_bit L i (by norm_num : (5 : ℕ) < 8) hv, pt_bit L i (by norm_num : (6 : ℕ) < 8) hv,
    pt_bit L i (by norm_num : (7 : ℕ) < 8) hv, xsum]
  simp only [Bool.xor_assoc, Bool.false_xor, Bool.xor_false]

theorem plane_bit {p : Par} (hp : p ∈ params) {g : MulAut VM4} (hg : Realizes g p) {i : ℕ}
    (hi : i < 8) {v : ℕ} (hv : v < 256) :
    (plane (recL p) i).testBit v = (cmp p v).testBit i := by
  rw [plane_bit_gen _ i hv, cmp_eq_xs hg hv, testBit_xs]
  exact xsum_congr 8 fun k hk => by rw [testBit_recL hp hk hi, Bool.and_comm]

theorem orRec_bit (P : ℕ → ℕ) (v : ℕ) : ∀ m,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.lor ih (P i)) m : ℕ).testBit v = true ↔
      ∃ i < m, (P i).testBit v = true
  | 0 => by simp
  | m + 1 => by
    change (_ ||| P m).testBit v = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, orRec_bit P v m]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem orRec_lt (P : ℕ → ℕ) (hP : ∀ i, P i < 2 ^ 256) : ∀ m,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.lor ih (P i)) m : ℕ) < 2 ^ 256
  | 0 => Nat.two_pow_pos _
  | m + 1 => Nat.or_lt_two_pow (orRec_lt P hP m) (hP m)

theorem FULLk_eq : CFSG.KC.L34Q.FULL = 2 ^ 256 - 1 := by
  unfold CFSG.KC.L34Q.FULL
  norm_num

theorem ne_zero_iff_bit {y : ℕ} (hy : y < 256) : y ≠ 0 ↔ ∃ i < 8, y.testBit i = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    refine ⟨i, ?_, hi⟩
    by_contra hge
    have : y.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [this] at hi
    exact absurd hi (by decide)
  · rintro ⟨i, -, hi⟩ rfl
    simp at hi

theorem kerMask_eq {p : Par} (hp : p ∈ params) {g : MulAut VM4} (hg : Realizes g p) :
    kerMask (recL p) = fixM p := by
  apply Nat.eq_of_testBit_eq
  intro v
  have hX := orRec_lt (plane (recL p)) (plane_lt (recL p)) 8
  unfold kerMask
  change (CFSG.KC.L34Q.FULL - _).testBit v = _
  rw [FULLk_eq, Nat.sub_sub, Nat.add_comm 1, Nat.testBit_two_pow_sub_succ hX]
  unfold fixM
  rw [testBit_maskOf]
  by_cases hv : v < 256
  · have hv' : v < 256 := hv
    simp only [hv, decide_true, Bool.true_and]
    have e : (Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.lor ih (plane (recL p) i)) 8 :
        ℕ).testBit v = !(act p v == v) := by
      apply Bool.eq_iff_iff.mpr
      rw [orRec_bit]
      constructor
      · rintro ⟨i, hi, h⟩
        rw [plane_bit hp hg hi hv'] at h
        have : cmp p v ≠ 0 := (ne_zero_iff_bit (cmp_lt p hv')).mpr ⟨i, hi, h⟩
        unfold cmp at this
        rw [Ne, xor_eq_zero_iff] at this
        simpa using this
      · intro h
        have : cmp p v ≠ 0 := by
          unfold cmp
          rw [Ne, xor_eq_zero_iff]
          simpa using h
        obtain ⟨i, hi, h⟩ := (ne_zero_iff_bit (cmp_lt p hv')).mp this
        exact ⟨i, hi, by rw [plane_bit hp hg hi hv']; exact h⟩
    rw [e, Bool.not_not]
  · simp [hv]

theorem lo_eq : ∀ j < 8, CFSG.KC.L34Q.FULL - BP.getD j 0 = loTab.getD j 0 := by
  decide +kernel

@[expose] noncomputable def xstep (w j M : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) M
    (letN M fun M => letN (Nat.sub CFSG.KC.L34Q.FULL (BP.getD j 0)) fun lo => Nat.lor
      (Nat.shiftLeft (Nat.land M lo) (Nat.shiftLeft 1 j))
      (Nat.land (Nat.shiftRight M (Nat.shiftLeft 1 j)) lo))
    (Nat.blt 0 (Nat.land w (Nat.shiftLeft 1 j)))

theorem xlate_eq_steps (M w : ℕ) : xlate M w = xstep w 7 (xstep w 6 (xstep w 5 (xstep w 4
    (xstep w 3 (xstep w 2 (xstep w 1 (xstep w 0 M))))))) := rfl

theorem xstep_eq (w : ℕ) {j : ℕ} (hj : j < 8) (M : ℕ) :
    xstep w j M = if w.testBit j then tr1 M j else M := by
  unfold xstep tr1
  rw [blt_and, letN_eq, letN_eq]
  have e := lo_eq j hj
  change CFSG.KC.L34Q.FULL - BP.getD j 0 = _ at e
  cases w.testBit j
  · rfl
  · simp only [↓reduceIte]
    rw [shl1_eq]
    change ((M &&& (CFSG.KC.L34Q.FULL - BP.getD j 0)) <<< 2 ^ j) |||
      ((M >>> 2 ^ j) &&& (CFSG.KC.L34Q.FULL - BP.getD j 0)) = _
    rw [e]

theorem xlate_eq (M w : ℕ) : xlate M w = transB M w 8 := by
  rw [xlate_eq_steps]
  simp only [xstep_eq w (by norm_num : (0 : ℕ) < 8), xstep_eq w (by norm_num : (1 : ℕ) < 8),
    xstep_eq w (by norm_num : (2 : ℕ) < 8), xstep_eq w (by norm_num : (3 : ℕ) < 8),
    xstep_eq w (by norm_num : (4 : ℕ) < 8), xstep_eq w (by norm_num : (5 : ℕ) < 8),
    xstep_eq w (by norm_num : (6 : ℕ) < 8), xstep_eq w (by norm_num : (7 : ℕ) < 8)]
  rfl

theorem high_bit : ∀ k < 8, ∀ u < 256, 256 ≤ u + 2 ^ k → u.testBit k = true := by
  decide +kernel

theorem tr1_high (m : ℕ) {k : ℕ} (hk : k < 8) {v : ℕ} (hv : 256 ≤ v) :
    (tr1 m k).testBit v = false := by
  unfold tr1
  rw [loTab_getD hk, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_shiftRight, testBit_lo, testBit_lo]
  have h1 : decide (v < 256) = false := by simp; omega
  rw [h1]
  by_cases h2 : v ≥ 2 ^ k
  · by_cases h3 : v - 2 ^ k < 256
    · have := high_bit k hk (v - 2 ^ k) h3 (by omega)
      simp [this]
    · simp [h3]
  · simp [h2]

theorem transB_high (m w : ℕ) (hm : ∀ v, 256 ≤ v → m.testBit v = false) : ∀ j, j ≤ 8 →
    ∀ v, 256 ≤ v → (transB m w j).testBit v = false
  | 0, _, v, hv => hm v hv
  | j + 1, hj, v, hv => by
    unfold transB
    split
    · exact tr1_high _ (by omega) hv
    · exact transB_high m w hm j (by omega) v hv

theorem mset_high (S : Set VM4) {v : ℕ} (hv : 256 ≤ v) : (mset S).testBit v = false := by
  cases h : (mset S).testBit v
  · rfl
  · have := ((testBit_mset S v).mp h).1
    omega

theorem or_xlate_mset (U : Subgroup VM4) {w : ℕ} (hw : w < 256) :
    Nat.lor (mset (U : Set VM4)) (xlate (mset (U : Set VM4)) w) = sumOne (mset (U : Set VM4)) w := by
  apply Nat.eq_of_testBit_eq
  intro v
  change (mset (U : Set VM4) ||| xlate _ w).testBit v = _
  rw [testBit_sumOne _ hw, Nat.testBit_or, xlate_eq]
  by_cases hv : v < 256
  · rw [testBit_transB _ _ le_rfl hv, Nat.mod_eq_of_lt (by norm_num; exact hw)]
    simp [hv]
  · have hv' : 256 ≤ v := by omega
    rw [mset_high _ hv', transB_high _ _ (fun u hu => mset_high _ hu) 8 le_rfl v hv']
    simp [hv]

@[expose] def spanK (bs : List ℕ) : Subgroup VM4 :=
  Subgroup.closure {y | ∃ b ∈ bs, Multiplicative.ofAdd (decode b) = y}

@[expose] def cols (p : Par) : List ℕ := (List.range 8).map fun k => cmp p (2 ^ k)

theorem spanAdd_aux {p : Par} (hp : p ∈ params) (U : Subgroup VM4) : ∀ n, n ≤ 8 →
    (Nat.rec (motive := fun _ => ℕ) (mset (U : Set VM4)) (fun k ih => letN ih fun M =>
      Nat.lor M (xlate M (Nat.land (Nat.shiftRight (recL p) (Nat.mul 8 k)) 255))) n : ℕ) =
      mset ((U ⊔ spanK ((List.range n).map fun k => cmp p (2 ^ k)) : Subgroup VM4) : Set VM4)
  | 0, _ => by
    have : spanK ([] : List ℕ) = ⊥ := by
      unfold spanK
      simp
    simp [this]
  | n + 1, hn => by
    change letN _ _ = _
    rw [letN_eq, spanAdd_aux hp U n (by omega)]
    beta_reduce
    have hn8 : n < 8 := by omega
    rw [lane_recL hp hn8, or_xlate_mset _ (cmp_lt p (pow_lt_256 hn8)),
      sumOne_mset _ (cmp_lt p (pow_lt_256 hn8))]
    congr 2
    have e : spanK ((List.range (n + 1)).map fun k => cmp p (2 ^ k)) =
        spanK ((List.range n).map fun k => cmp p (2 ^ k)) ⊔
          Subgroup.closure {Multiplicative.ofAdd (decode (cmp p (2 ^ n)))} := by
      unfold spanK
      rw [← Subgroup.closure_union]
      congr 1
      ext y
      simp [List.range_succ, or_comm, eq_comm]
    rw [e, sup_assoc]

theorem spanAdd_eq {p : Par} (hp : p ∈ params) (U : Subgroup VM4) :
    spanAdd (mset (U : Set VM4)) (recL p) = mset ((U ⊔ spanK (cols p) : Subgroup VM4) : Set VM4) :=
  spanAdd_aux hp U 8 le_rfl

theorem comm_code {g : MulAut VM4} {p : Par} (hg : Realizes g p) {v : ℕ} (hv : v < 256) :
    Multiplicative.ofAdd (decode (cmp p v)) =
      g (Multiplicative.ofAdd (decode v)) * (Multiplicative.ofAdd (decode v))⁻¹ := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_comm hg, toAdd_ofAdd, toAdd_ofAdd]
  unfold cmp act
  rw [← decode_code (gmap p.A p.B p.s p.t (decode v) + decode v), code_add, code_decode hv]

theorem xs_mem {g : MulAut VM4} {p : Par} (hg : Realizes g p) (v : ℕ) : ∀ n, n ≤ 8 →
    Multiplicative.ofAdd (decode (xs (cmp p) v n)) ∈ spanK (cols p)
  | 0, _ => by
    rw [xs, decode_zero]
    exact Subgroup.one_mem _
  | n + 1, hn => by
    have h1 : xs (cmp p) v n < 256 :=
      xs_lt v n (by omega) fun k hk => cmp_lt p (pow_lt_256 (k := k) (by omega))
    have h2 : (if v.testBit n then cmp p (2 ^ n) else 0) < 256 := by
      split
      · exact cmp_lt p (pow_lt_256 (k := n) (by omega))
      · norm_num
    rw [xs, decode_xor h1 h2, ofAdd_add]
    refine Subgroup.mul_mem _ (xs_mem hg v n (by omega)) ?_
    split
    · apply Subgroup.subset_closure
      refine ⟨cmp p (2 ^ n), ?_, rfl⟩
      unfold cols
      exact List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩
    · rw [decode_zero]
      exact Subgroup.one_mem _

theorem closure_comm_eq {g : MulAut VM4} {p : Par} (hg : Realizes g p) :
    Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} = spanK (cols p) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    have hv := code_lt (Multiplicative.toAdd x)
    have e := comm_code hg hv
    rw [decode_code, ofAdd_toAdd] at e
    rw [← e, cmp_eq_xs hg hv]
    exact xs_mem hg _ 8 le_rfl
  · unfold spanK
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, rfl⟩
    unfold cols at hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    apply Subgroup.subset_closure
    exact ⟨_, (comm_code hg (pow_lt_256 (List.mem_range.mp hk))).symm⟩

theorem comM_eq_mset {g : MulAut VM4} {p : Par} (hg : Realizes g p) :
    comM p = mset (Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} : Set VM4) := by
  classical
  let Cg : Subgroup VM4 :=
    { carrier := {y | ∃ x, g x * x⁻¹ = y}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a * b, ?_⟩
        rw [map_mul, inv_vm4, inv_vm4, inv_vm4]
        rw [mul_mul_mul_comm]
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, by rw [inv_vm4 (g a * a⁻¹)]⟩ }
  have hCg : Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} = Cg :=
    le_antisymm ((Subgroup.closure_le Cg).mpr fun y hy => hy) Subgroup.subset_closure
  rw [hCg]
  apply Nat.eq_of_testBit_eq
  intro w
  apply Bool.eq_iff_iff.mpr
  rw [testBit_mset]
  constructor
  · intro hw
    obtain ⟨hw1, x, hx⟩ := exists_of_testBit_comM hg hw
    exact ⟨hw1, ⟨x, hx.symm⟩⟩
  · rintro ⟨hw1, x, hx⟩
    have := testBit_comM_of hg x
    rwa [hx, toAdd_ofAdd, code_decode hw1] at this

theorem imMask_eq {p : Par} (hp : p ∈ params) {g : MulAut VM4} (hg : Realizes g p) :
    imMask (recL p) = comM p := by
  unfold imMask
  have h := spanAdd_eq hp ⊥
  rw [mset_bot, bot_sup_eq] at h
  rw [h, comM_eq_mset hg, closure_comm_eq hg]

theorem spanAdd_mset {p : Par} (hp : p ∈ params) {g : MulAut VM4} (hg : Realizes g p)
    (U : Subgroup VM4) :
    spanAdd (mset (U : Set VM4)) (recL p) =
      mset ((U ⊔ Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} : Subgroup VM4) : Set VM4) := by
  rw [spanAdd_eq hp, closure_comm_eq hg]

@[expose] noncomputable def recP (p : Par) : ℕ × (ℕ × ℕ) := (recL p, (fixM p, comM p))

@[expose] noncomputable def matJ (j : ℕ) : ℕ :=
  matN (Nat.div j 432) (Nat.succ (Nat.mod (Nat.div j 144) 3))
    (Nat.succ (Nat.mod (Nat.div j 48) 3)) (Nat.mod (Nat.div j 12) 4)
    (Nat.succ (Nat.mod (Nat.div j 4) 3)) (Nat.mod (Nat.div j 2) 2) (Nat.mod j 2)

theorem mem_brec {α : Type} {x y : α} {l : List α} (h : x ∈ l) (b : Bool) :
    x ∈ (Bool.rec (motive := fun _ => List α) l (y :: l) b) := by
  cases b
  · exact h
  · exact List.mem_cons_of_mem _ h

theorem mem_rec_aux : ∀ n, ∀ i < n,
    mulF2 8 (matJ (Nat.sub 1727 i)) (matJ (Nat.sub 1727 i)) = IDQ →
    ((Nat.xor (matJ (Nat.sub 1727 i)) IDQ, (kerMask (Nat.xor (matJ (Nat.sub 1727 i)) IDQ),
      imMask (Nat.xor (matJ (Nat.sub 1727 i)) IDQ))) : ℕ × (ℕ × ℕ)) ∈
    (Nat.rec (motive := fun _ => List (ℕ × (ℕ × ℕ))) [] (fun i ih =>
    letRec (Nat.sub 1727 i) fun j =>
    letRec (matN (Nat.div j 432) (Nat.succ (Nat.mod (Nat.div j 144) 3))
        (Nat.succ (Nat.mod (Nat.div j 48) 3)) (Nat.mod (Nat.div j 12) 4)
        (Nat.succ (Nat.mod (Nat.div j 4) 3)) (Nat.mod (Nat.div j 2) 2) (Nat.mod j 2)) fun M =>
      Bool.rec (motive := fun _ => List (ℕ × (ℕ × ℕ))) ih
        (letRec (Nat.xor M IDQ) fun L => List.cons (L, (kerMask L, imMask L)) ih)
        (Nat.beq (mulF2 8 M M) IDQ)) n : List (ℕ × (ℕ × ℕ)))
  | 0, i, hi, _ => absurd hi (by omega)
  | n + 1, i, hi, h => by
    unfold matJ at h ⊢
    dsimp only
    rw [letRec_eq]
    beta_reduce
    rw [letRec_eq]
    beta_reduce
    rw [letRec_eq]
    beta_reduce
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hin
    · have ih := mem_rec_aux n i hi (by unfold matJ; exact h)
      unfold matJ at ih
      exact mem_brec ih _
    · subst hin
      have hb : Nat.beq (mulF2 8 (matN (Nat.div (Nat.sub 1727 i) 432)
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 144) 3))
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 48) 3))
          (Nat.mod (Nat.div (Nat.sub 1727 i) 12) 4)
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 4) 3))
          (Nat.mod (Nat.div (Nat.sub 1727 i) 2) 2) (Nat.mod (Nat.sub 1727 i) 2))
          (matN (Nat.div (Nat.sub 1727 i) 432)
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 144) 3))
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 48) 3))
          (Nat.mod (Nat.div (Nat.sub 1727 i) 12) 4)
          (Nat.succ (Nat.mod (Nat.div (Nat.sub 1727 i) 4) 3))
          (Nat.mod (Nat.div (Nat.sub 1727 i) 2) 2) (Nat.mod (Nat.sub 1727 i) 2))) IDQ = true := by
        rw [Nat.beq_eq]
        exact h
      rw [hb]
      exact List.mem_cons_self ..

theorem nz_bounds : ∀ x ∈ nzF4, 1 ≤ x.code.val ∧ x.code.val ≤ 3 := by
  intro x hx
  simp only [nzF4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem mem_invRecsK {g : MulAut VM4} {p : Par} (hp : p ∈ params) (hg : Realizes g p)
    (h2 : g * g = 1) : recP p ∈ invRecsK := by
  have hm := mulF2_matP hp hg h2
  obtain ⟨a, a', b1, b, b2, s, t, ha', hb1, hb2, hpe⟩ := params_shape hp
  set j := t.toNat + 2 * s.toNat + 4 * (b2.code.val - 1) + 12 * b.code.val +
    48 * (b1.code.val - 1) + 144 * (a'.code.val - 1) + 432 * a.code.val with hj
  have ea := a.code.isLt
  have eb := b.code.isLt
  have e1 := nz_bounds a' ha'
  have e2 := nz_bounds b1 hb1
  have e3 := nz_bounds b2 hb2
  have es : s.toNat ≤ 1 := Bool.toNat_le s
  have et : t.toNat ≤ 1 := Bool.toNat_le t
  have hjlt : j < 1728 := by omega
  have hmat : matJ j = matP p := by
    rw [hpe]
    unfold matJ matP
    have hd : ∀ x y : ℕ, Nat.div x y = x / y := fun _ _ => rfl
    have hmo : ∀ x y : ℕ, Nat.mod x y = x % y := fun _ _ => rfl
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, hd, hmo, Nat.succ_eq_add_one]
    congr 1 <;> omega
  have hi : Nat.sub 1727 (1727 - j) = j := by rw [Nat.sub_eq]; omega
  have h := mem_rec_aux 1728 (1727 - j) (by omega) (by rw [hi, hmat]; exact hm)
  rw [hi, hmat] at h
  change (recL p, (kerMask (recL p), imMask (recL p))) ∈ _ at h
  unfold recP
  rw [← kerMask_eq hp hg, ← imMask_eq hp hg]
  unfold invRecsK
  exact h

theorem FULL_eq : FULL = CFSG.KC.L34Q.FULL := by decide +kernel

theorem capOKK_spec {D : List (ℕ × (ℕ × ℕ))} {R : List ℕ} (h : capOKK D R = true) :
    CFSG.KC.L34Q.FULL ∈ R ∧ ∀ W ∈ R, (∀ d ∈ D, subB d.2.2 W = true → W &&& d.2.1 ∈ R) ∧
      countK D W ^ 4 * popK W ^ 3 ≤ 2 ^ 24 := by
  unfold capOKK at h
  rw [brec_and, Bool.and_eq_true] at h
  refine ⟨memL_mem h.1, fun W hW => ?_⟩
  have h1 := allR_mem h.2 W hW
  beta_reduce at h1
  rw [brec_and, Bool.and_eq_true] at h1
  refine ⟨?_, Nat.le_of_ble_eq_true h1.2⟩
  have key : ∀ D' : List (ℕ × (ℕ × ℕ)), capStepB D' R W = true →
      ∀ d ∈ D', subB d.2.2 W = true → W &&& d.2.1 ∈ R := by
    intro D'
    induction D' with
    | nil => intro _ d hd; simp at hd
    | cons d0 D' ih =>
      intro hs d hd hsub
      obtain ⟨L0, fx0, cm0⟩ := d0
      change Bool.rec (motive := fun _ => Bool) false (capStepB D' R W)
        (Bool.rec (motive := fun _ => Bool) true (memL (Nat.land W fx0) R) (subB cm0 W)) = true
        at hs
      rw [brec_and, brec_imp, Bool.and_eq_true] at hs
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [hsub] at hs
        exact memL_mem (by simpa using hs.1)
      · exact ih hs.2 d hd hsub
  exact key D h1.1

theorem plusOKK_spec {D : List (ℕ × (ℕ × ℕ))} {R : List ℕ} (h : plusOKK D R = true) :
    1 ∈ R ∧ ∀ U ∈ R, (∀ d ∈ D, subB U d.2.1 = true → spanAdd U d.1 ∈ R) ∧
      (U = 1 ∨ countK D U < popK U) := by
  unfold plusOKK at h
  rw [brec_and, Bool.and_eq_true] at h
  refine ⟨memL_mem h.1, fun U hU => ?_⟩
  have h1 := allR_mem h.2 U hU
  beta_reduce at h1
  rw [brec_and, Bool.and_eq_true] at h1
  refine ⟨?_, ?_⟩
  · have key : ∀ D' : List (ℕ × (ℕ × ℕ)), plusStepB D' R U = true →
        ∀ d ∈ D', subB U d.2.1 = true → spanAdd U d.1 ∈ R := by
      intro D'
      induction D' with
      | nil => intro _ d hd; simp at hd
      | cons d0 D' ih =>
        intro hs d hd hsub
        obtain ⟨L0, fx0, cm0⟩ := d0
        change Bool.rec (motive := fun _ => Bool) false (plusStepB D' R U)
          (Bool.rec (motive := fun _ => Bool) true (memL (spanAdd U L0) R) (subB U fx0)) = true
          at hs
        rw [brec_and, brec_imp, Bool.and_eq_true] at hs
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [hsub] at hs
          exact memL_mem (by simpa using hs.1)
        · exact ih hs.2 d hd hsub
    exact key D h1.1
  · have h2 := h1.2
    rw [brec_or, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h2
    exact h2

theorem card_le_countK {D : List (ℕ × (ℕ × ℕ))} (hD : D = invRecsK) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) {W : Set VM4}
    (h1 : ∀ g ∈ E, ∀ x ∈ W, g x = x) (h2 : ∀ g ∈ E, ∀ x, g x * x⁻¹ ∈ W) :
    Nat.card E ≤ countK D (mset W) := by
  classical
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  set P : ℕ × (ℕ × ℕ) → Bool := fun d => subB (mset W) d.2.1 && subB d.2.2 (mset W) with hP
  have hcard : Nat.card E = hfin.toFinset.card := Nat.card_eq_card_finite_toFinset hfin
  rw [hcard, countK_eq, List.countP_eq_length_filter]
  let f : MulAut VM4 → Par := fun g =>
    if h : ∃ p ∈ params, Realizes g p then h.choose else ⟨1, 1, false, false⟩
  have hf : ∀ g ∈ E, f g ∈ params ∧ Realizes g (f g) := by
    intro g hg
    have h := hE g hg
    simp only [f, h, ↓reduceDIte]
    exact h.choose_spec
  have hmaps : ∀ g ∈ hfin.toFinset, recP (f g) ∈ (D.filter P).toFinset := by
    intro g hg
    have hgE : g ∈ E := hfin.mem_toFinset.mp hg
    obtain ⟨hp, hr⟩ := hf g hgE
    have h2' : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
    rw [List.mem_toFinset, List.mem_filter, hD]
    refine ⟨mem_invRecsK hp hr h2', ?_⟩
    have he := elat_of hr (h1 g hgE) (h2 g hgE)
    simp only [elat, dataOf, Bool.and_eq_true, beq_iff_eq] at he
    simp only [hP, recP, Bool.and_eq_true, subB_iff]
    exact he
  have hinj : Set.InjOn (fun g => recP (f g)) hfin.toFinset := by
    intro g hg g' hg' hgg
    have hgE : g ∈ E := hfin.mem_toFinset.mp hg
    have hgE' : g' ∈ E := hfin.mem_toFinset.mp hg'
    obtain ⟨hp, hr⟩ := hf g hgE
    obtain ⟨hp', hr'⟩ := hf g' hgE'
    have hL : recL (f g) = recL (f g') := congrArg Prod.fst hgg
    have hcol : ∀ k < 8, act (f g) (2 ^ k) = act (f g') (2 ^ k) := by
      intro k hk
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 8
      · have a1 := testBit_matP hp hk hi
        have a2 := testBit_matP hp' hk hi
        have : matP (f g) = matP (f g') := by
          have := congrArg (· ^^^ IDQ) hL
          simpa [recL, Nat.xor_assoc] using this
        rw [← a1, ← a2, this]
      · have b1 : (act (f g) (2 ^ k)).testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (act_lt _ _) (by
            calc 256 = 2 ^ 8 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
        have b2 : (act (f g') (2 ^ k)).testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (act_lt _ _) (by
            calc 256 = 2 ^ 8 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [b1, b2]
    refine MulEquiv.ext fun x => ?_
    have hv := code_lt (Multiplicative.toAdd x)
    have e1 := act_eq_of_realizes hr (v := code (Multiplicative.toAdd x))
    have e2 := act_eq_of_realizes hr' (v := code (Multiplicative.toAdd x))
    rw [decode_code, ofAdd_toAdd] at e1 e2
    have e3 : act (f g) (code (Multiplicative.toAdd x)) = act (f g') (code (Multiplicative.toAdd x)) := by
      rw [act_eq_xs hr hv, act_eq_xs hr' hv, xs_congr _ 8 hcol]
    rw [e1, e2] at e3
    have e4 := congrArg decode e3
    rw [decode_code, decode_code] at e4
    exact Multiplicative.toAdd.injective e4
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans (List.toFinset_card_le _)

@[expose] def fixK (S : Finset (MulAut VM4)) : Set VM4 := {x | ∀ g ∈ S, g x = x}

theorem mset_fixK_empty : mset (fixK ∅) = FULL := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [testBit_mset', testBit_FULL]
  simp [fixK]

theorem mset_fixK_insert {g : MulAut VM4} {p : Par} (hg : Realizes g p)
    (S : Finset (MulAut VM4)) : mset (fixK (insert g S)) = mset (fixK S) &&& fixM p := by
  classical
  apply Nat.eq_of_testBit_eq
  intro v
  rw [Nat.testBit_and, testBit_mset', testBit_mset']
  unfold fixM
  rw [testBit_maskOf]
  by_cases hv : v < 256
  · have h := act_eq_self_iff hg hv
    by_cases hgv : g (Multiplicative.ofAdd (decode v)) = Multiplicative.ofAdd (decode v)
    · have h' : (act p v == v) = true := beq_iff_eq.mpr (h.mpr hgv)
      simp only [hv, decide_true, Bool.true_and, h', Bool.and_true]
      congr 1
      simp only [fixK, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, hgv, true_and]
    · have h' : (act p v == v) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h2 => hgv (h.mp h2)
      simp only [hv, decide_true, Bool.true_and, h', Bool.and_false]
      simp only [fixK, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, hgv, false_and,
        decide_false]
  · simp [hv]

theorem fixK_eq_fixV {E : Subgroup (MulAut VM4)} {S : Finset (MulAut VM4)}
    (hS : ∀ g, g ∈ S ↔ g ∈ E) : fixK S = (fixV E : Set VM4) := by
  ext x
  simp only [fixK, Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixV, hS]

@[expose] def cmK (S : Finset (MulAut VM4)) : Subgroup VM4 :=
  Subgroup.closure {y | ∃ g ∈ S, ∃ x, g x * x⁻¹ = y}

theorem cmK_insert (g : MulAut VM4) (S : Finset (MulAut VM4)) :
    cmK (insert g S) = cmK S ⊔ Subgroup.closure {y | ∃ x, g x * x⁻¹ = y} := by
  classical
  unfold cmK
  rw [← Subgroup.closure_union]
  congr 1
  ext y
  simp only [Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨g', hg' | hg', x, rfl⟩
    · subst hg'; exact Or.inr ⟨x, rfl⟩
    · exact Or.inl ⟨g', hg', x, rfl⟩
  · rintro (⟨g', hg', x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨g', Or.inr hg', x, rfl⟩
    · exact ⟨g, Or.inl rfl, x, rfl⟩

theorem cmK_empty : cmK ∅ = ⊥ := by
  unfold cmK
  simp

theorem cmK_eq_commV {E : Subgroup (MulAut VM4)} {S : Finset (MulAut VM4)}
    (hS : ∀ g, g ∈ S ↔ g ∈ E) : cmK S = commV E := by
  unfold cmK commV
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, hS]

theorem fixV_mem {D : List (ℕ × (ℕ × ℕ))} {R : List ℕ} (hD : D = invRecsK)
    (hR : capOKK D R = true) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) (hq : IsQuadratic E) :
    mset (fixV E : Set VM4) ∈ R := by
  classical
  obtain ⟨h0, hcl⟩ := capOKK_spec hR
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  have key : ∀ S : Finset (MulAut VM4), (∀ g ∈ S, g ∈ E) → mset (fixK S) ∈ R := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [mset_fixK_empty, FULL_eq]
      exact h0
    | insert g S hgS ih =>
      intro hS
      have hgE : g ∈ E := hS g (Finset.mem_insert_self g S)
      have ih' := ih fun g' hg' => hS g' (Finset.mem_insert_of_mem hg')
      obtain ⟨p, hp, hr⟩ := hE g hgE
      have h2 : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
      have hd : recP p ∈ D := hD ▸ mem_invRecsK hp hr h2
      have hsub : subB (recP p).2.2 (mset (fixK S)) = true := by
        rw [subB_iff]
        apply Nat.eq_of_testBit_eq
        intro w
        rw [Nat.testBit_and]
        simp only [recP]
        cases hw : (comM p).testBit w
        · rfl
        · obtain ⟨hw1, x, hx⟩ := exists_of_testBit_comM hr hw
          have hmem : g x * x⁻¹ ∈ fixV E := hq (Subgroup.subset_closure ⟨g, hgE, x, rfl⟩)
          have : (mset (fixK S)).testBit w = true := by
            rw [testBit_mset]
            refine ⟨hw1, ?_⟩
            rw [hx]
            simp only [fixK, Set.mem_setOf_eq]
            intro g' hg'
            exact (mem_fixV.mp hmem) g' (hS g' (Finset.mem_insert_of_mem hg'))
          rw [this]
          rfl
      have h3 := (hcl _ ih').1 _ hd hsub
      simp only [recP] at h3
      rw [mset_fixK_insert hr]
      exact h3
  have := key hfin.toFinset fun g hg => hfin.mem_toFinset.mp hg
  rwa [fixK_eq_fixV fun g => hfin.mem_toFinset] at this

theorem commV_mem {D : List (ℕ × (ℕ × ℕ))} {R : List ℕ} (hD : D = invRecsK)
    (hR : plusOKK D R = true) {E : Subgroup (MulAut VM4)}
    (hE : ∀ g ∈ E, ∃ p ∈ params, Realizes g p) (hel : IsElemAbelian2 E) (hq : IsQuadratic E) :
    mset (commV E : Set VM4) ∈ R := by
  classical
  obtain ⟨h0, hcl⟩ := plusOKK_spec hR
  have hfin : (E : Set (MulAut VM4)).Finite := Set.toFinite _
  have key : ∀ S : Finset (MulAut VM4), (∀ g ∈ S, g ∈ E) → mset (cmK S : Set VM4) ∈ R := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [cmK_empty, mset_bot]
      exact h0
    | insert g S hgS ih =>
      intro hS
      have hgE : g ∈ E := hS g (Finset.mem_insert_self g S)
      have ih' := ih fun g' hg' => hS g' (Finset.mem_insert_of_mem hg')
      obtain ⟨p, hp, hr⟩ := hE g hgE
      have h2 : g * g = 1 := by rw [← pow_two]; exact hel.2 g hgE
      have hd : recP p ∈ D := hD ▸ mem_invRecsK hp hr h2
      have hle : cmK S ≤ commV E := by
        unfold cmK commV
        apply Subgroup.closure_mono
        rintro _ ⟨g', hg', x, rfl⟩
        exact ⟨g', hS g' (Finset.mem_insert_of_mem hg'), x, rfl⟩
      have hsub : subB (mset (cmK S : Set VM4)) (recP p).2.1 = true := by
        rw [subB_iff]
        apply Nat.eq_of_testBit_eq
        intro v
        rw [Nat.testBit_and]
        cases hv : (mset (cmK S : Set VM4)).testBit v
        · rfl
        · obtain ⟨hv1, hv2⟩ := (testBit_mset _ v).mp hv
          have hfix : Multiplicative.ofAdd (decode v) ∈ fixV E := hq (hle hv2)
          simp only [recP]
          unfold fixM
          rw [testBit_maskOf]
          simp only [hv1, decide_true, Bool.true_and, beq_iff_eq]
          exact (act_eq_self_iff hr hv1).mpr ((mem_fixV.mp hfix) g hgE)
      have h3 := (hcl _ ih').1 _ hd hsub
      simp only [recP] at h3
      rw [spanAdd_mset hp hr] at h3
      rw [cmK_insert]
      exact h3
  have := key hfin.toFinset fun g hg => hfin.mem_toFinset.mp hg
  rwa [cmK_eq_commV fun g => hfin.mem_toFinset] at this

theorem facts_of_checks {D : List (ℕ × (ℕ × ℕ))} {R R2 : List ℕ}
    (hD : eqRecs invRecsK D = true) (hR : capOKK D R = true) (hR2 : plusOKK D R2 = true) :
    (∀ E : Subgroup (MulAut VM4), (∀ g ∈ E, ∃ p ∈ params, Realizes g p) → IsElemAbelian2 E →
      IsQuadratic E → Nat.card E ^ 4 * Nat.card (fixV E) ^ 3 ≤ 2 ^ 24) ∧
    (∀ E : Subgroup (MulAut VM4), (∀ g ∈ E, ∃ p ∈ params, Realizes g p) → IsElemAbelian2 E →
      IsQuadratic E → E ≠ ⊥ → Nat.card E < Nat.card (commV E)) := by
  classical
  have hD' : D = invRecsK := (eqRecs_eq _ _ hD).symm
  constructor
  · intro E hE hel hq
    have hW := fixV_mem hD' hR hE hel hq
    have hbd := ((capOKK_spec hR).2 _ hW).2
    have hc := card_le_countK hD' hE hel (W := (fixV E : Set VM4))
      (fun g hg x hx => (mem_fixV.mp hx) g hg)
      (fun g hg x => hq (Subgroup.subset_closure ⟨g, hg, x, rfl⟩))
    rw [popK_eq, popcount_mset] at hbd
    calc Nat.card E ^ 4 * Nat.card (fixV E) ^ 3
        ≤ countK D (mset (fixV E : Set VM4)) ^ 4 * Nat.card (fixV E : Set VM4) ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc 4)
      _ ≤ 2 ^ 24 := hbd
  · intro E hE hel hq hne
    have hU := commV_mem hD' hR2 hE hel hq
    have hbd := ((plusOKK_spec hR2).2 _ hU).2
    have hc := card_le_countK hD' hE hel (W := (commV E : Set VM4))
      (fun g hg x hx => (mem_fixV.mp (hq hx)) g hg)
      (fun g hg x => Subgroup.subset_closure ⟨g, hg, x, rfl⟩)
    rcases hbd with h1 | hbd
    · exfalso
      apply hne
      have hU0 : commV E = ⊥ := by
        rw [← mset_bot] at h1
        exact SetLike.coe_injective (mset_injective h1)
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun x => ?_
      have hx : g x * x⁻¹ ∈ commV E := Subgroup.subset_closure ⟨g, hg, x, rfl⟩
      rw [hU0, Subgroup.mem_bot, mul_inv_eq_one] at hx
      exact hx
    · rw [popK_eq, popcount_mset] at hbd
      exact lt_of_le_of_lt hc hbd

end CFSG.Quasithin.H13.Ch9.L34Q.KS
