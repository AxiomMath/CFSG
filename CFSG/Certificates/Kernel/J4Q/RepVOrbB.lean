module

public import CFSG.Certificates.Kernel.J4Q.RepVOrb
public import Certificates.Data.Kernel.J4Q.VOrbB
import CFSG.Certificates.Kernel.J4Q.VOrbBFS
import CFSG.Certificates.Kernel.J4Q.VOrbTree
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.KC.LQT.Syl CFSG.KS.PackFld

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq'' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem rowJ_bit (rm Z r j : Nat) :
    (rowJ rm Z r).testBit j = (Z.testBit (r * 128 + j) && rm.testBit j) := by
  change ((Z >>> (r * 128)) &&& rm).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]

private theorem rowJ_fld {Z : Nat} {g : Nat → Nat} (h : Fld 128 Z g) (r : Nat) :
    rowJ (2 ^ 112 - 1) Z r = g r &&& (2 ^ 112 - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowJ_bit, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 112
  · rw [Nat.mul_comm, h r j (by omega)]
  · simp [hj]

private theorem rowJ_xor (rm a b r : Nat) : rowJ rm (a ^^^ b) r = rowJ rm a r ^^^ rowJ rm b r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowJ_bit, Nat.testBit_xor, Nat.testBit_xor, rowJ_bit, rowJ_bit]
  cases a.testBit (r * 128 + j) <;> cases b.testBit (r * 128 + j) <;> cases rm.testBit j <;> rfl

private theorem rowJ_and (rm a b r : Nat) : rowJ rm (a &&& b) r = rowJ rm a r &&& rowJ rm b r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowJ_bit, Nat.testBit_and, Nat.testBit_and, rowJ_bit, rowJ_bit]
  cases a.testBit (r * 128 + j) <;> cases b.testBit (r * 128 + j) <;> cases rm.testBit j <;> rfl

private theorem rowJ_zero (rm r : Nat) : rowJ rm 0 r = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowJ_bit, Nat.zero_testBit, Nat.zero_testBit, Bool.false_and]

private theorem rowJ_xsum (rm r : Nat) (f : Nat → Nat) : ∀ n,
    rowJ rm (xsum f n) r = xsum (fun k => rowJ rm (f k) r) n
  | 0 => rowJ_zero rm r
  | n + 1 => by rw [xsum_succ, xsum_succ, rowJ_xor, rowJ_xsum rm r f n]

private noncomputable def bsum (h : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc + h i * 2 ^ (128 * i)) n

private theorem bsum_succ (h : Nat → Nat) (n : Nat) :
    bsum h (n + 1) = bsum h n + h n * 2 ^ (128 * n) := rfl

private theorem fld_bsum {h : Nat → Nat} (hh : ∀ i, h i < 2 ^ 128) : ∀ n,
    Fld 128 (bsum h n) (fun i => if i < n then h i else 0) ∧ bsum h n < 2 ^ (128 * n)
  | 0 => ⟨fld_congr (fld_zero 128) (fun i => by simp), by simp [bsum]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := fld_bsum hh n
    have e : bsum h (n + 1) = h n <<< (128 * n) ||| bsum h n := by
      rw [bsum_succ, Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt ih2]
    refine ⟨?_, ?_⟩
    · rw [e]
      refine fld_congr (fld_or (fld_shl n (fld_one (hh n))) ih1) ?_
      intro i
      by_cases h1 : i < n
      · have h2 : ¬ n ≤ i := by omega
        have h3 : i < n + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h2 : i = n
        · subst h2
          simp
        · have h3 : ¬ i < n + 1 := by omega
          have h4 : ¬ i - n = 0 := by omega
          simp [h1, h3, h4]
    · rw [bsum_succ]
      have h3 : h n * 2 ^ (128 * n) + 2 ^ (128 * n) ≤ 2 ^ 128 * 2 ^ (128 * n) := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (hh n)
      rw [Nat.mul_succ, Nat.add_comm (128 * n) 128, Nat.pow_add]
      omega

private theorem bsum_mul (h : Nat → Nat) (v : Nat) : ∀ n,
    bsum h n * v = bsum (fun i => h i * v) n
  | 0 => by simp [bsum]
  | n + 1 => by
    rw [bsum_succ, bsum_succ, Nat.add_mul, bsum_mul h v n, Nat.mul_right_comm]

private theorem fld_eq {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hY : Fld w Y g) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hd := Nat.div_add_mod p w
  rw [← hd, hX _ _ (Nat.mod_lt _ hw), hY _ _ (Nat.mod_lt _ hw)]

private theorem rep_eq_bsum : ∀ n, rep 1 128 n = bsum (fun _ => 1) n
  | 0 => rfl
  | n + 1 => by
    have h2 := (fld_bsum (h := fun _ => 1) (fun _ => by omega) n).2
    change rep 1 128 n ||| 1 <<< (128 * n) = bsum (fun _ => 1) n + 1 * 2 ^ (128 * n)
    rw [rep_eq_bsum n, Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt h2,
      Nat.lor_comm]

private theorem one_bit (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
  simp [eq_comm]

private theorem and_rep (X n : Nat) :
    X &&& rep 1 128 n = bsum (fun i => if X.testBit (128 * i) then 1 else 0) n := by
  have hb : ∀ i, (if X.testBit (128 * i) then 1 else 0) < 2 ^ 128 := fun i => by split <;> omega
  refine fld_eq (by omega : 0 < 128) ?_ (fld_bsum hb n).1
  have hr := (fld_bsum (h := fun _ => 1) (fun _ => by omega) n).1
  rw [← rep_eq_bsum] at hr
  intro i k hk
  rw [Nat.testBit_and, hr i k hk]
  by_cases hi : i < n
  · simp only [hi, if_true]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · cases hX : X.testBit (128 * i) <;> simp [hX]
    · have hk1 : k ≠ 0 := by omega
      cases X.testBit (128 * i) <;> simp [one_bit, hk1]
  · simp [hi]

private noncomputable def stepQ (c rm a b k : Nat) : Nat :=
  ((a >>> k) &&& c) * rm &&& ((b >>> (k * 128)) &&& rm) * c

private theorem mrec_eq (c rm a b : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => mstep c rm a b acc k) n = xsum (stepQ c rm a b) n
  | 0 => rfl
  | n + 1 => by
    change mstep c rm a b (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => mstep c rm a b acc k) n) n = _
    rw [mrec_eq c rm a b n]
    rfl

private theorem mulJ_xsum (c rm a b : Nat) : mulJ c rm a b = xsum (stepQ c rm a b) 112 := by
  unfold mulJ
  rw [strictN_eq'', strictN_eq'']
  exact mrec_eq c rm a b (nat_lit 112)

private theorem rowJ_stepQ {n r k : Nat} (hr : r < n) (hk : k < 112) (A M : Nat) :
    rowJ (2 ^ 112 - 1) (stepQ (rep 1 128 n) (2 ^ 112 - 1) A M k) r =
      ((rowJ (2 ^ 112 - 1) A r >>> k) &&& 1) * rowJ (2 ^ 112 - 1) M k := by
  have hc : (2 : Nat) ^ 112 - 1 < 2 ^ 128 := by norm_num
  have hY : rowJ (2 ^ 112 - 1) M k < 2 ^ 112 :=
    Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos 112) Nat.one_pos)
  have hY1 : rowJ (2 ^ 112 - 1) M k &&& (2 ^ 112 - 1) = rowJ (2 ^ 112 - 1) M k :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hY
  have hY2 : (2 ^ 112 - 1) &&& rowJ (2 ^ 112 - 1) M k = rowJ (2 ^ 112 - 1) M k := by
    rw [Nat.and_comm, hY1]
  have e1 : ((A >>> k) &&& rep 1 128 n) * (2 ^ 112 - 1) =
      bsum (fun i => (if (A >>> k).testBit (128 * i) then 1 else 0) * (2 ^ 112 - 1)) n := by
    rw [and_rep, bsum_mul]
  have e2 : rowJ (2 ^ 112 - 1) M k * rep 1 128 n = bsum (fun _ => rowJ (2 ^ 112 - 1) M k) n := by
    rw [rep_eq_bsum, Nat.mul_comm, bsum_mul]
    simp only [Nat.one_mul]
  have hb1 : ∀ i, (if (A >>> k).testBit (128 * i) then 1 else 0) * (2 ^ 112 - 1) < 2 ^ 128 :=
    fun i => by
      split
      · rw [Nat.one_mul]
        exact hc
      · rw [Nat.zero_mul]
        exact Nat.two_pow_pos 128
  have hb2 : ∀ _ : Nat, rowJ (2 ^ 112 - 1) M k < 2 ^ 128 := fun _ => Nat.lt_trans hY (by norm_num)
  change rowJ (2 ^ 112 - 1) (((A >>> k) &&& rep 1 128 n) * (2 ^ 112 - 1) &&&
    rowJ (2 ^ 112 - 1) M k * rep 1 128 n) r = _
  rw [rowJ_and, e1, e2, rowJ_fld (fld_bsum hb1 n).1, rowJ_fld (fld_bsum hb2 n).1, if_pos hr,
    if_pos hr, and_one_bit]
  have hb : (rowJ (2 ^ 112 - 1) A r).testBit k = (A >>> k).testBit (128 * r) := by
    rw [rowJ_bit, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, decide_eq_true hk,
      Bool.and_true, Nat.mul_comm, Nat.add_comm]
  rw [hb]
  generalize rowJ (2 ^ 112 - 1) M k = Y at hY1 hY2 ⊢
  generalize (2 : Nat) ^ 112 - 1 = m at hY1 hY2 ⊢
  cases (A >>> k).testBit (128 * r) <;> simp [hY1, hY2]

theorem rowJ_mulJ {n r : Nat} (hr : r < n) (A M : Nat) :
    rowJ (2 ^ 112 - 1) (mulJ (rep 1 128 n) (2 ^ 112 - 1) A M) r =
      vecJ (2 ^ 112 - 1) (rowJ (2 ^ 112 - 1) A r) M := by
  rw [mulJ_xsum, rowJ_xsum, vecJ_eq]
  exact xsum_congr (fun k hk => rowJ_stepQ hr hk A M)

theorem rowJ_packK {m : Nat} (hm : m < 2 ^ 128) : ∀ (l : List Nat) (r : Nat),
    rowJ m (packK m l) r = l.getD r 0 &&& m
  | [], r => by
    rw [List.getD_nil, Nat.zero_and]
    exact rowJ_zero _ r
  | x :: t, r => by
    have e : packK m (x :: t) = (x &&& m) ||| (packK m t <<< 128) := rfl
    rw [e]
    cases r with
    | zero =>
      apply Nat.eq_of_testBit_eq
      intro j
      rw [rowJ_bit, List.getD_cons_zero, Nat.testBit_or, Nat.testBit_and, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.zero_mul, Nat.zero_add]
      by_cases hj : 128 ≤ j
      · have hmj : m.testBit j = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hj))
        rw [hmj, Bool.and_false, Bool.and_false]
      · have hj' : decide (j ≥ 128) = false := decide_eq_false hj
        rw [hj', Bool.false_and, Bool.or_false]
        cases x.testBit j <;> cases m.testBit j <;> rfl
    | succ r =>
      rw [List.getD_cons_succ, ← rowJ_packK hm t r]
      apply Nat.eq_of_testBit_eq
      intro j
      rw [rowJ_bit, rowJ_bit, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
      have hX : m.testBit ((r + 1) * 128 + j) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : decide ((r + 1) * 128 + j ≥ 128) = true := decide_eq_true (by omega)
      have h3 : (r + 1) * 128 + j - 128 = r * 128 + j := by omega
      rw [hX, Bool.and_false, Bool.false_or, h2, Bool.true_and, h3]

theorem vecJ_land (x M : Nat) : vecJ (2 ^ 112 - 1) (x &&& (2 ^ 112 - 1)) M = vecJ (2 ^ 112 - 1) x M := by
  rw [vecJ_eq, vecJ_eq]
  apply xsum_congr
  intro k hk
  have hk' : k < 112 := hk
  rw [and_one_bit, and_one_bit, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hk',
    Bool.and_true]

private theorem rowsL_eq (rm q : Nat) (tl : List Nat) : ∀ (l : List Nat) (k : Nat),
    rowsL rm q l k tl = (List.range' k l.length).map (rowJ rm q) ++ tl
  | [], _ => rfl
  | _ :: l, k => by
    change rowJ rm q k :: rowsL rm q l (k + 1) tl = _
    rw [rowsL_eq rm q tl l (k + 1), List.length_cons, List.range'_succ, List.map_cons,
      List.cons_append]

private theorem clGo_sound {rm c a : Nat} {pc SP : List Nat} : ∀ (Ms acc : List Nat),
    clGo rm c a pc SP Ms acc = true →
      (∀ y ∈ acc, y ∈ SP) ∧ ∀ M ∈ Ms, ∀ r < pc.length, rowJ rm (mulJ c rm a M) r ∈ SP
  | [], acc, h => ⟨VOrbTree.inSK_sound h, fun _ hM => (List.not_mem_nil hM).elim⟩
  | M :: Ms, acc, h => by
    change strictB (mulJ c rm a M) (fun q => clGo rm c a pc SP Ms (rowsL rm q pc 0 acc)) = true at h
    rw [strictB_eq'] at h
    obtain ⟨h1, h2⟩ := clGo_sound Ms _ h
    rw [rowsL_eq] at h1
    refine ⟨fun y hy => h1 y (List.mem_append_right _ hy), ?_⟩
    intro M' hM' r hr
    rcases List.mem_cons.1 hM' with rfl | hM'
    · exact h1 _ (List.mem_append_left _
        (List.mem_map.2 ⟨r, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩))
    · exact h2 M' hM' r hr

theorem clB_sound {rm N : Nat} (hrm : rm = 2 ^ 112 - 1) {Ms pc SP : List Nat} (hN : pc.length ≤ N)
    (h : clB rm (rep 1 128 N) Ms pc SP = true) : ∀ x ∈ pc, ∀ M ∈ Ms, vecJ rm x M ∈ SP := by
  subst hrm
  unfold clB at h
  rw [strictB_eq', strictB_eq'] at h
  have h2 := (clGo_sound _ _ h).2
  intro x hx M hM
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hx
  have h3 := h2 M hM r hr
  rwa [rowJ_mulJ (by omega), rowJ_packK (by norm_num), List.getD_eq_getElem _ _ hr, vecJ_land]
    at h3

theorem diffAll_eq : ∀ (SQ : List (List Nat)) (sc : List Nat),
    diffAll sc SQ = SQ.foldl (fun acc s => diffS acc s) sc
  | [], _ => rfl
  | s :: SQ, sc => diffAll_eq SQ (diffS sc s)

private theorem andB_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem eqLK_sound : ∀ {xs ys : List Nat}, eqLK xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | x :: xs, y :: ys, h => by
    change andB (Nat.beq x y) (eqLK xs ys) = true at h
    obtain ⟨hxy, htail⟩ := (andB_true _ _).1 h
    rw [Nat.eq_of_beq_eq_true hxy, eqLK_sound htail]

theorem inSK_of_sorted {pc s SP : List Nat} (h : eqLK (sortN pc) s = true)
    (h2 : eqLK (diffS s SP) [] = true) : inSK pc SP = true := by
  unfold inSK
  rw [eqLK_sound h]
  exact h2

theorem spInK_of_sorted {sc : List Nat} {Pch SQ : List (List Nat)} (h : Pch.map sortN = SQ)
    (h2 : eqLK (diffAll sc SQ) [] = true) : spInK sc Pch = true := by
  unfold spInK
  rw [diffAll_eq, ← h, List.foldl_map] at h2
  exact h2

private theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | _ :: _, 0 => rfl
  | m :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact getN_eq d l i

private theorem dropK_eq : ∀ (n : Nat) (l : List Nat), dropK n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    change List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) (dropK n l) = _
    rw [dropK_eq n l, ← List.tail_drop]
    cases l.drop n <;> rfl

private theorem headK_drop (n : Nat) (l : List Nat) : headK (l.drop n) = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop n <;> rfl

private theorem ordGo_unfold (nl e : Nat) (ch : List Nat) (ci k : Nat) :
    ordGo nl (e :: ch) ci k = true ↔ ci ≤ e >>> 114 ∧ e >>> 114 < k ∧ (e >>> 112) &&& 3 < nl ∧
      ordGo nl ch (e >>> 114) (k + 1) = true := by
  change andB (Nat.ble ci (Nat.shiftRight e 114)) (andB (Nat.blt (Nat.shiftRight e 114) k)
    (andB (Nat.blt (Nat.land (Nat.shiftRight e 112) 3) nl)
      (ordGo nl ch (Nat.shiftRight e 114) (k + 1)))) = true ↔ _
  simp only [andB_true, Nat.ble_eq, Nat.blt_eq]
  rfl

private theorem ordGo_spec (nl : Nat) : ∀ (ch : List Nat) (ci k : Nat), ordGo nl ch ci k = true →
    ∀ j < ch.length, ch.getD j 0 >>> 114 < k + j ∧ (ch.getD j 0 >>> 112) &&& 3 < nl
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | e :: ch, ci, k, h, j, hj => by
    obtain ⟨_, h2, h3, h4⟩ := (ordGo_unfold nl e ch ci k).1 h
    cases j with
    | zero => exact ⟨by simpa using h2, by simpa using h3⟩
    | succ j =>
      obtain ⟨h5, h6⟩ := ordGo_spec nl ch _ (k + 1) h4 j (by simpa using hj)
      rw [List.getD_cons_succ]
      exact ⟨by omega, h6⟩

private theorem ppGo_eq (nl : Nat) (P : List Nat) : ∀ (ch : List Nat) (ci k : Nat),
    ordGo nl ch ci k = true → ppGo ch (P.drop ci) ci = ch.map (fun e => P.getD (e >>> 114) 0)
  | [], _, _, _ => rfl
  | e :: ch, ci, k, h => by
    obtain ⟨h1, _, _, h4⟩ := (ordGo_unfold nl e ch ci k).1 h
    change headK (dropK (e >>> 114 - ci) (P.drop ci)) ::
      ppGo ch (dropK (e >>> 114 - ci) (P.drop ci)) (e >>> 114) = _
    have hd : dropK (e >>> 114 - ci) (P.drop ci) = P.drop (e >>> 114) := by
      rw [dropK_eq, List.drop_drop, Nat.add_sub_cancel' h1]
    rw [hd, ppGo_eq nl P ch _ (k + 1) h4, headK_drop, List.map_cons]

private theorem rowChk_sound (rm Q g : Nat) : ∀ (ch : List Nat) (j₀ : Nat), rowChk rm Q g ch j₀ = true →
    ∀ j < ch.length, (ch.getD j 0 >>> 112) &&& 3 = g → rowJ rm Q (j₀ + j) = ch.getD j 0 &&& rm
  | [], _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | e :: ch, j₀, h, j, hj, hl => by
    change Bool.rec (motive := fun _ => Bool) (rowChk rm Q g ch (j₀ + 1))
      (andB (Nat.beq (rowJ rm Q j₀) (Nat.land e rm)) (rowChk rm Q g ch (j₀ + 1)))
      (Nat.beq (Nat.land (Nat.shiftRight e 112) 3) g) = true at h
    have ht : rowChk rm Q g ch (j₀ + 1) = true := by
      cases hb : Nat.beq (Nat.land (Nat.shiftRight e 112) 3) g <;> rw [hb] at h
      · exact h
      · exact ((andB_true _ _).1 h).2
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hl ⊢
      have hb : Nat.beq (Nat.land (Nat.shiftRight e 112) 3) g = true := Nat.beq_eq_true_eq _ _ ▸ hl
      rw [hb] at h
      exact Nat.eq_of_beq_eq_true ((andB_true _ _).1 h).1
    | succ j =>
      rw [List.getD_cons_succ] at hl ⊢
      rw [← Nat.add_assoc, Nat.add_right_comm]
      exact rowChk_sound rm Q g ch (j₀ + 1) ht j (by simpa using hj) hl

private theorem trGo_sound (rm c a : Nat) (ch : List Nat) : ∀ (Ms : List Nat) (g₀ : Nat),
    trGo rm c a ch Ms g₀ = true → ∀ j < ch.length, ∀ g < Ms.length,
      (ch.getD j 0 >>> 112) &&& 3 = g₀ + g → rowJ rm (mulJ c rm a (Ms.getD g 0)) j = ch.getD j 0 &&& rm
  | [], _, _, _, _, g, hg, _ => absurd hg (Nat.not_lt_zero _)
  | M :: Ms, g₀, h, j, hj, g, hg, hl => by
    change andB (strictB (mulJ c rm a M) fun q => rowChk rm q g₀ ch 0) (trGo rm c a ch Ms (g₀ + 1))
      = true at h
    obtain ⟨h1, h2⟩ := (andB_true _ _).1 h
    rw [strictB_eq'] at h1
    cases g with
    | zero =>
      have := rowChk_sound rm _ g₀ ch 0 h1 j hj hl
      rwa [Nat.zero_add] at this
    | succ g =>
      rw [List.getD_cons_succ]
      exact trGo_sound rm c a ch Ms (g₀ + 1) h2 j hj g (by simpa using hg) (by omega)

theorem vtB_sound {rm N : Nat} (hrm : rm = 2 ^ 112 - 1) {Ms P ch : List Nat} {p₀ k₀ : Nat}
    (hN : ch.length ≤ N) (h : vtB rm (rep 1 128 N) Ms P ch p₀ k₀ = true) :
    ∀ j < ch.length, ch.getD j 0 >>> 114 < k₀ + j ∧ (ch.getD j 0 >>> 112) &&& 3 < Ms.length ∧
      vecJ rm (P.getD (ch.getD j 0 >>> 114) 0) (Ms.getD ((ch.getD j 0 >>> 112) &&& 3) 0) =
        Nat.land (ch.getD j 0) rm := by
  subst hrm
  unfold vtB at h
  obtain ⟨ho, ht⟩ := (andB_true _ _).1 h
  rw [strictB_eq', strictB_eq', dropK_eq, ppGo_eq _ P ch p₀ k₀ ho] at ht
  intro j hj
  obtain ⟨hp, hl⟩ := ordGo_spec _ ch p₀ k₀ ho j hj
  refine ⟨hp, hl, ?_⟩
  have h3 := trGo_sound _ _ _ ch Ms 0 ht j hj _ hl (Nat.zero_add _).symm
  have hj' : j < (ch.map (fun e => P.getD (e >>> 114) 0)).length := by rw [List.length_map]; exact hj
  rw [rowJ_mulJ (by omega), rowJ_packK (by norm_num), List.getD_eq_getElem _ _ hj',
    List.getElem_map, vecJ_land, ← List.getD_eq_getElem _ 0 hj] at h3
  exact h3

private theorem flatten_index {B : Nat} : ∀ {chs : List (List Nat)},
    (∀ i, i + 1 < chs.length → (chs.getD i []).length = B) →
    ∀ t < chs.flatten.length, ∃ i < chs.length, ∃ j < (chs.getD i []).length,
      t = B * i + j ∧ chs.flatten.getD t 0 = (chs.getD i []).getD j 0
  | [], _, t, ht => by simp at ht
  | c :: cs, hB, t, ht => by
    rw [List.flatten_cons, List.length_append] at ht
    by_cases htc : t < c.length
    · refine ⟨0, by simp, t, by simpa using htc, by simp, ?_⟩
      rw [List.flatten_cons, List.getD_append _ _ _ _ htc]
      rfl
    · have hcs : cs ≠ [] := by
        rintro rfl
        simp at ht
        omega
      have hcB : c.length = B := by
        have := hB 0 (by simpa using List.length_pos_of_ne_nil hcs)
        simpa using this
      obtain ⟨i, hi, j, hj, he, hg⟩ := flatten_index (chs := cs)
        (fun i hi => by simpa using hB (i + 1) (by simpa using hi)) (t - c.length) (by omega)
      refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega)]
        simpa using hg

theorem vtBs_sound {rm root B cap : Nat} (hrm : rm = 2 ^ 112 - 1) {Ms : List Nat}
    {Rs : List (List Nat)} (hR : Rs = Ms.map (rowsOfJ rm)) {chs : List (List Nat)} {p0s : List Nat}
    (_hlen : chs.flatten.length + 1 = cap)
    (_hchs : ∀ i, i + 1 < chs.length → (chs.getD i []).length = B)
    (_hlast : ∀ ch ∈ chs, ch.length ≤ B)
    (_htree : ∀ i < chs.length, vtB rm (rep 1 128 B) Ms (vptsK rm root chs.flatten)
      (chs.getD i []) (p0s.getD i 0) (1 + B * i) = true) :
    ∀ k, 0 < k → k < cap →
      Nat.shiftRight (chs.flatten.getD (k - 1) 0) 114 < k ∧
      Nat.land (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 112) 3 < Rs.length ∧
      vecLJ ((vptsK rm root chs.flatten).getD (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 114) 0)
        (Rs.getD (Nat.land (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 112) 3) []) =
        (vptsK rm root chs.flatten).getD k 0 := by
  intro k hk0 hk
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have htl : t < chs.flatten.length := by omega
  obtain ⟨i, hi, j, hj, htij, hg⟩ := flatten_index _hchs t htl
  have hN : (chs.getD i []).length ≤ B := by
    rw [List.getD_eq_getElem _ _ hi]
    exact _hlast _ (List.getElem_mem _)
  obtain ⟨hpar, hlab, he⟩ := vtB_sound hrm hN (_htree i hi) j hj
  have hRl : Rs.length = Ms.length := by rw [hR, List.length_map]
  have hsucc : (vptsK rm root chs.flatten).getD (t + 1) 0 = Nat.land (chs.flatten.getD t 0) rm := by
    unfold vptsK
    rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact htl),
      List.getElem_map, List.getD_eq_getElem _ _ htl]
  rw [hsucc, hg]
  refine ⟨Nat.lt_of_lt_of_le hpar (by omega), by rw [hRl]; exact hlab, ?_⟩
  have hRs : Rs.getD ((chs.getD i []).getD j 0 >>> 112 &&& 3) [] =
      rowsOfJ rm (Ms.getD ((chs.getD i []).getD j 0 >>> 112 &&& 3) 0) := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hlab]
    simp only [hR, List.getElem_map]
  change vecLJ _ (Rs.getD ((chs.getD i []).getD j 0 >>> 112 &&& 3) []) = _
  rw [hRs, vecLJ_rowsOfJ]
  exact he

theorem vorbit_soundB (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats : Array (Array V2)}
    {Ms : List Nat} (_hs : mats.size = Ms.length)
    (_hM : ∀ g, WfA (mats[g]?.getD (idRows ())) ∧ encR (mats[g]?.getD (idRows ())) = getN one Ms g)
    {w : V2} (_hw : w.wf = true) {cap bits : Nat} (_hcap : cap < 2 ^ bits)
    (_h32 : 4 * 2 ^ bits < 2 ^ 32)
    {Rs : List (List Nat)} (_hR : Rs = Ms.map (rowsOfJ rm)) {B : Nat} (_hB : Ms.length * B ≤ 131072)
    (_hB1 : 0 < B)
    {chs : List (List Nat)} {p0s : List Nat} {SPch : List (List Nat)}
    (_hlen : chs.flatten.length + 1 = cap)
    (_hchs : ∀ i, i + 1 < chs.length → (chs.getD i []).length = B)
    (_hlast : ∀ ch ∈ chs, ch.length ≤ B)
    (_htree : ∀ i < chs.length, vtB rm (rep 1 128 B) Ms (vptsK rm (v2N w) chs.flatten)
      (chs.getD i []) (p0s.getD i 0) (1 + B * i) = true)
    (_hsinc : sincK SPch.flatten 0 = true) (_hsl : SPch.flatten.length = cap)
    (_hspl : ∀ sc ∈ SPch, sc.length ≤ 131072)
    (_hin : ∀ pc ∈ pchK rm (v2N w) chs, inSK pc SPch.flatten = true)
    (_hsp : ∀ sc ∈ SPch, spInK sc (pchK rm (v2N w) chs) = true)
    (_hcl : ∀ pc ∈ pchK rm (v2N w) chs, clB rm (rep 1 128 B) Ms pc SPch.flatten = true) :
    vorbOK (mats.map frTable) w (vorbit (mats.map frTable) w cap bits) cap = true := by
  have hrm : rm = 2 ^ 112 - 1 := (consts_c _hK).2
  set ts := mats.map frTable with hts
  set A := vptsK rm (v2N w) chs.flatten with hA
  have hAP : (pchK rm (v2N w) chs).flatten = A := by
    simp only [pchK, List.flatten_cons, List.singleton_append, hA, vptsK, List.map_flatten]
  have htsz : ts.size = Ms.length := by rw [hts, Array.size_map, _hs]
  have hRl : Rs.length = Ms.length := by rw [_hR, List.length_map]
  have hact : ∀ v : V2, v.wf = true → ∀ g < ts.size,
      (frApply ts[g]! v).wf = true ∧ v2N (frApply ts[g]! v) = vecLJ (v2N v) (Rs.getD g []) := by
    intro v hv g hg
    have hgm : g < mats.size := by rw [hts, Array.size_map] at hg; exact hg
    have hget : ts[g]! = frTable mats[g] := by
      rw [getElem!_pos ts g hg]
      simp only [hts, Array.getElem_map]
    have hMg := _hM g
    rw [Array.getElem?_eq_getElem hgm, Option.getD_some] at hMg
    rw [hget]
    refine ⟨wf_frApply hMg.1 v, ?_⟩
    have hMs : Ms.getD g one = Ms[g]'(by omega) := List.getD_eq_getElem _ _ (by omega)
    have hRs : Rs.getD g [] = rowsOfJ rm (Ms[g]'(by omega)) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [_hR, List.getElem_map]
    rw [v2N_frApply _hK hMg.1 hv, hMg.2, getN_eq, hMs, hRs, vecLJ_rowsOfJ]
  have hpts := VOrbTree.checked_points_spec (Pch := pchK rm (v2N w) chs) (cap := cap)
    (by rw [hAP, hA, vptsK, List.length_cons, List.length_map, _hlen]) _hsl _hsinc _hsp
  rw [hAP] at hpts
  have hmem := VOrbTree.checked_membership _hin _hsp
  rw [hAP] at hmem
  have hclA : ∀ x ∈ A, ∀ g < Ms.length, vecLJ x (Rs.getD g []) ∈ A := by
    intro x hx g hg
    rw [← hAP] at hx
    obtain ⟨pc, hpc, hx⟩ := List.mem_flatten.1 hx
    have hlen : pc.length ≤ B := by
      simp only [pchK, List.mem_cons, List.mem_map] at hpc
      rcases hpc with rfl | ⟨ch, hch, rfl⟩
      · rw [List.length_singleton]
        exact _hB1
      · rw [List.length_map]
        exact _hlast ch hch
    have hRs : Rs.getD g [] = rowsOfJ rm (Ms[g]'hg) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [_hR, List.getElem_map]
    rw [hRs, vecLJ_rowsOfJ]
    exact (hmem _).2 (clB_sound hrm hlen (_hcl pc hpc) x hx _ (List.getElem_mem _))
  have htr : ∀ k, 0 < k → k < A.length → ∃ par < k, ∃ lab < Rs.length,
      A.getD k 0 = vecLJ (A.getD par 0) (Rs.getD lab []) := by
    intro k hk0 hk
    have hAl : A.length = cap := by rw [hA, vptsK, List.length_cons, List.length_map, _hlen]
    obtain ⟨h1, h2, h3⟩ := vtBs_sound hrm _hR _hlen _hchs _hlast _htree k hk0 (by omega)
    exact ⟨_, h1, _, h2, h3.symm⟩
  have hreach : ∀ S : Nat → Prop, S (v2N w) →
      (∀ v, S (v2N v) → ∀ g < ts.size, S (v2N (frApply ts[g]! v))) → ∀ x ∈ A, S x := by
    intro S h0 hstep
    have hall : ∀ k, k < A.length → S (A.getD k 0) ∧ ∃ v : V2, v.wf = true ∧ v2N v = A.getD k 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · exact ⟨h0, w, _hw, rfl⟩
        · obtain ⟨par, hpar, lab, hlab, he⟩ := htr k hk0 hk
          obtain ⟨hS, v, hv, hvp⟩ := ih par hpar (by omega)
          have hlt : lab < ts.size := by omega
          obtain ⟨hw', hn⟩ := hact v hv lab hlt
          rw [he, ← hvp, ← hn]
          rw [← hvp] at hS
          exact ⟨hstep v hS lab hlt, _, hw', rfl⟩
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [← List.getD_eq_getElem _ 0 hk]
    exact (hall k hk).1
  refine VOrbBFS.vorbit_ok _h32 _hcap hpts.2.1
    ((List.toFinset_card_of_nodup hpts.2.1).symm.trans hpts.2.2) _hw
    (by rw [hA, vptsK]; exact List.mem_cons_self)
    (fun v hv g hg => (hact v hv g hg).1) (fun v hv hvA g hg => ?_) hreach
  · rw [(hact v hv g hg).2]
    exact hclA _ hvA g (by omega)

end CFSG.KC.J4Q

end
