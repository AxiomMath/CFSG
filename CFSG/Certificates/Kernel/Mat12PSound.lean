module

public import Certificates.Data.Kernel.Mat12P
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CFSG.KC.Mat12P

open CFSG.Quasithin.H13.MatNCert CFSG.KC.Mat8P

@[expose] def lanesQ : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ 12 * lanesQ n

theorem testBit_one_addQ (K j : ℕ) :
    (1 + 2 ^ 12 * K).testBit j = if j < 12 then decide (j = 0) else K.testBit (j - 12) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add K (by norm_num)]
  split_ifs with h
  · rcases j with _ | j
    · simp
    · simp [Nat.testBit_succ]
  · rfl

theorem and_lanes_succQ (Z K : ℕ) :
    Z &&& (1 + 2 ^ 12 * K) = (Z &&& 1) + 2 ^ 12 * ((Z >>> 12) &&& K) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : Z &&& 1 < 2 ^ 12 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  rw [Nat.testBit_and, testBit_one_addQ, Nat.add_comm (Z &&& 1),
    Nat.testBit_two_pow_mul_add _ h1]
  split_ifs with h
  · rw [Nat.testBit_and]
    rcases j with _ | j
    · simp
    · simp [Nat.testBit_succ]
  · rw [Nat.testBit_and, Nat.testBit_shiftRight]
    congr 2
    omega

theorem and_one_mul_testBitQ (Z c b : ℕ) :
    ((Z &&& 1) * c).testBit b = (Z.testBit 0 && c.testBit b) := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one Z with h | h
  · have : Z.testBit 0 = false := by simp [Nat.testBit_zero, h]
    simp [h, this]
  · have : Z.testBit 0 = true := by simp [Nat.testBit_zero, h]
    simp [h, this]

theorem lanes_mul_testBitQ : ∀ (n Z c : ℕ), c < 2 ^ 12 → ∀ j b, b < 12 →
    ((Z &&& lanesQ n) * c).testBit (12 * j + b) =
      (decide (j < n) && Z.testBit (12 * j) && c.testBit b)
  | 0, Z, c, _, j, b, _ => by simp [lanesQ]
  | n + 1, Z, c, hc, j, b, hb => by
    rw [lanesQ, and_lanes_succQ, Nat.add_mul, Nat.mul_assoc]
    have h1 : (Z &&& 1) * c < 2 ^ 12 := by
      have : Z &&& 1 ≤ 1 := Nat.and_le_right
      calc (Z &&& 1) * c ≤ 1 * c := Nat.mul_le_mul_right c this
        _ < 2 ^ 12 := by omega
    rw [Nat.add_comm ((Z &&& 1) * c), Nat.testBit_two_pow_mul_add _ h1]
    rcases j with _ | j
    · simp only [Nat.mul_zero, Nat.zero_add, hb, if_true, and_one_mul_testBitQ Z c b]
      simp
    · have hj : ¬ (12 * (j + 1) + b < 12) := by omega
      rw [if_neg hj, show 12 * (j + 1) + b - 12 = 12 * j + b by omega,
        lanes_mul_testBitQ n (Z >>> 12) c hc j b hb, Nat.testBit_shiftRight]
      rw [show 12 + 12 * j = 12 * (j + 1) by omega]
      simp

theorem lanesQ_twelve : lanesQ 12 = 5445847423328601499764522166702896582657 := by decide

theorem testBit_4095 (b : ℕ) : (4095 : ℕ).testBit b = decide (b < 12) := by
  by_cases hb : b < 12
  · interval_cases b <;> decide
  · rw [Nat.testBit_eq_false_of_lt]
    · simp [hb]
    · calc (4095 : ℕ) < 2 ^ 12 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem colQ_def (X s : ℕ) : colQ X s = (X >>> s) &&& 4095 := rfl

theorem colQ_testBit (X s b : ℕ) :
    (colQ X s).testBit b = (decide (b < 12) && X.testBit (s + b)) := by
  rw [colQ_def, Nat.testBit_and, Nat.testBit_shiftRight, testBit_4095, Bool.and_comm]

theorem colQ_lt (X s : ℕ) : colQ X s < 2 ^ 12 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem termQ_def (X Y i s : ℕ) : termQ X Y i s = ((Y >>> i) &&& lanesQ 12) * colQ X s := by
  rw [lanesQ_twelve]
  rfl

theorem termQ_testBit (X Y i s j b : ℕ) (hs : s = 12 * i) (hj : j < 12) (hb : b < 12) :
    (termQ X Y i s).testBit (12 * j + b) = (Y.testBit (12 * j + i) && X.testBit (12 * i + b)) := by
  rw [termQ_def, lanes_mul_testBitQ 12 _ _ (colQ_lt X s) j b hb, Nat.testBit_shiftRight,
    colQ_testBit, hs]
  simp only [hj, hb, decide_true, Bool.true_and]
  rw [Nat.add_comm i]

theorem mulQ_eq (X Y : ℕ) : mulQ X Y =
    termQ X Y 0 0 ^^^ (termQ X Y 1 12 ^^^ (termQ X Y 2 24 ^^^ (termQ X Y 3 36 ^^^
    (termQ X Y 4 48 ^^^ (termQ X Y 5 60 ^^^ (termQ X Y 6 72 ^^^ (termQ X Y 7 84 ^^^
    (termQ X Y 8 96 ^^^ (termQ X Y 9 108 ^^^ (termQ X Y 10 120 ^^^ termQ X Y 11 132)))))))))) :=
  rfl

theorem mvN_cons (c : ℕ) (A : List ℕ) (v : ℕ) :
    mvN (c :: A) v = (if v.testBit 0 then c else 0) ^^^ mvN A (v / 2) := rfl

theorem testBit_iteQ (c : Bool) (a b : ℕ) :
    (if c then a else 0).testBit b = (c && a.testBit b) := by
  cases c <;> simp

theorem mvN_lt : ∀ (A : List ℕ) (v : ℕ), (∀ c ∈ A, c < 2 ^ 12) → mvN A v < 2 ^ 12
  | [], _, _ => by simp [mvN]
  | c :: A, v, h => by
    rw [mvN_cons]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · exact h c List.mem_cons_self
      · positivity
    · exact mvN_lt A (v / 2) fun d hd => h d (List.mem_cons_of_mem _ hd)

theorem unpackQ_lt (X : ℕ) : ∀ c ∈ unpackQ X, c < 2 ^ 12 := by
  intro c hc
  simp only [unpackQ, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> exact colQ_lt _ _

theorem col_eqQ (X Y j : ℕ) (hj : j < 12) :
    mvN (unpackQ X) (colQ Y (12 * j)) = colQ (mulQ X Y) (12 * j) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 12
  · simp only [unpackQ, mvN_cons, mvN, Nat.testBit_xor, testBit_iteQ, Nat.testBit_div_two,
      colQ_testBit, mulQ_eq, hb, Nat.zero_testBit, decide_true, Bool.true_and]
    rw [termQ_testBit X Y 0 0 j b rfl hj hb, termQ_testBit X Y 1 12 j b rfl hj hb,
      termQ_testBit X Y 2 24 j b rfl hj hb, termQ_testBit X Y 3 36 j b rfl hj hb,
      termQ_testBit X Y 4 48 j b rfl hj hb, termQ_testBit X Y 5 60 j b rfl hj hb,
      termQ_testBit X Y 6 72 j b rfl hj hb, termQ_testBit X Y 7 84 j b rfl hj hb,
      termQ_testBit X Y 8 96 j b rfl hj hb, termQ_testBit X Y 9 108 j b rfl hj hb,
      termQ_testBit X Y 10 120 j b rfl hj hb, termQ_testBit X Y 11 132 j b rfl hj hb]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Bool.xor_false]
    norm_num
  · rw [colQ_testBit, decide_eq_false hb, Bool.false_and]
    apply Nat.testBit_eq_false_of_lt
    calc mvN (unpackQ X) (colQ Y (12 * j)) < 2 ^ 12 := mvN_lt _ _ (unpackQ_lt X)
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mulN_unpackQ (X Y : ℕ) : mulN (unpackQ X) (unpackQ Y) = unpackQ (mulQ X Y) := by
  have hY : unpackQ Y = [colQ Y (12 * 0), colQ Y (12 * 1), colQ Y (12 * 2), colQ Y (12 * 3),
      colQ Y (12 * 4), colQ Y (12 * 5), colQ Y (12 * 6), colQ Y (12 * 7), colQ Y (12 * 8),
      colQ Y (12 * 9), colQ Y (12 * 10), colQ Y (12 * 11)] := rfl
  have hZ : unpackQ (mulQ X Y) = [colQ (mulQ X Y) (12 * 0), colQ (mulQ X Y) (12 * 1),
      colQ (mulQ X Y) (12 * 2), colQ (mulQ X Y) (12 * 3), colQ (mulQ X Y) (12 * 4),
      colQ (mulQ X Y) (12 * 5), colQ (mulQ X Y) (12 * 6), colQ (mulQ X Y) (12 * 7),
      colQ (mulQ X Y) (12 * 8), colQ (mulQ X Y) (12 * 9), colQ (mulQ X Y) (12 * 10),
      colQ (mulQ X Y) (12 * 11)] := rfl
  rw [mulN, hY, hZ]
  simp only [List.map_cons, List.map_nil]
  rw [col_eqQ X Y 0 (by norm_num), col_eqQ X Y 1 (by norm_num), col_eqQ X Y 2 (by norm_num),
    col_eqQ X Y 3 (by norm_num), col_eqQ X Y 4 (by norm_num), col_eqQ X Y 5 (by norm_num),
    col_eqQ X Y 6 (by norm_num), col_eqQ X Y 7 (by norm_num), col_eqQ X Y 8 (by norm_num),
    col_eqQ X Y 9 (by norm_num), col_eqQ X Y 10 (by norm_num), col_eqQ X Y 11 (by norm_num)]

@[expose] def colsQ (X : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => colQ X 0 :: colsQ (X >>> 12) k

theorem unpackQ_cols (X : ℕ) : unpackQ X = colsQ X 12 := by
  simp only [colsQ, unpackQ, colQ_def, Nat.shiftRight_zero, ← Nat.shiftRight_add]

theorem colQ_zero (X : ℕ) : colQ X 0 = X % 4096 := by
  rw [colQ_def, Nat.shiftRight_zero, show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem codeQ_cons (c : ℕ) (A : List ℕ) : codeQ (c :: A) = c + 4096 * codeQ A := rfl

theorem codeQ_cols : ∀ (k X : ℕ), codeQ (colsQ X k) = X % 2 ^ (12 * k)
  | 0, X => by simp [colsQ, codeQ, Nat.mod_one]
  | k + 1, X => by
    rw [colsQ, codeQ_cons, codeQ_cols k, colQ_zero, Nat.shiftRight_eq_div_pow,
      show 12 * (k + 1) = 12 + 12 * k by ring, pow_add, Nat.mod_mul]
    norm_num

theorem colsQ_codeQ : ∀ (A : List ℕ), (∀ c ∈ A, c < 4096) → colsQ (codeQ A) A.length = A
  | [], _ => rfl
  | c :: A, h => by
    have hc : c < 4096 := h c List.mem_cons_self
    have e1 : (c + 4096 * codeQ A) % 4096 = c := by omega
    have e2 : (c + 4096 * codeQ A) / 2 ^ 12 = codeQ A := by norm_num; omega
    rw [List.length_cons, colsQ, codeQ_cons, colQ_zero, Nat.shiftRight_eq_div_pow, e1, e2,
      colsQ_codeQ A fun d hd => h d (List.mem_cons_of_mem _ hd)]

theorem codeL_toQ : codeL 12 = codeQ := by
  funext x
  induction x with
  | nil => rfl
  | cons c A ih =>
    rw [codeQ_cons, ← ih]
    rfl

theorem codeQ_unpackQ (X : ℕ) : codeQ (unpackQ X) = X % 2 ^ 144 := by
  rw [unpackQ_cols, codeQ_cols]

theorem validQ_eq (x : List ℕ) : validQ x = validB 12 x := by
  rw [Bool.eq_iff_iff]
  simp [validQ, validB, Nat.blt_eq]

theorem unpackQ_codeQ (A : List ℕ) (h : validB 12 A = true) : unpackQ (codeQ A) = A := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hc⟩ := h
  rw [unpackQ_cols, ← hl]
  exact colsQ_codeQ A fun c h => by simpa using hc c h

theorem unpackQ_inj {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144)
    (h : unpackQ X = unpackQ Y) : X = Y := by
  have := congrArg codeQ h
  rw [codeQ_unpackQ, codeQ_unpackQ, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY] at this
  exact this

theorem termQ_lt (X Y i s : ℕ) : termQ X Y i s < 2 ^ 144 := by
  have h1 : (Y >>> i) &&& lanesQ 12 ≤ lanesQ 12 := Nat.and_le_right
  have h2 : colQ X s ≤ 4095 := Nat.le_of_lt_succ (colQ_lt X s)
  rw [termQ_def]
  calc ((Y >>> i) &&& lanesQ 12) * colQ X s ≤ lanesQ 12 * 4095 := Nat.mul_le_mul h1 h2
    _ < 2 ^ 144 := by rw [lanesQ_twelve]; norm_num

theorem mulQ_lt (X Y : ℕ) : mulQ X Y < 2 ^ 144 := by
  rw [mulQ_eq]
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact termQ_lt _ _ _ _

theorem oneQ_eq : unpackQ oneQ = oneN 12 := by decide

theorem oneQ_lt : oneQ < 2 ^ 144 := by decide

theorem mvNR_eq : ∀ (A : List ℕ) (v : ℕ), mvNR A v = mvN A v
  | [], _ => rfl
  | c :: A, v => by
    have hb : Nat.mul c (Nat.land v 1) = if v.testBit 0 then c else 0 := by
      change c * (v &&& 1) = _
      rw [Nat.and_one_is_mod, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    have hs : Nat.shiftRight v 1 = v / 2 := by
      change v >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    rw [mvNR, mvN, hb, hs, mvNR_eq A]
    rfl

theorem mulNF_eq (A B : List ℕ) : mulNF A B = mulN A B := by
  rw [mulNF]
  split_ifs with h
  · rw [Bool.and_eq_true, validQ_eq, validQ_eq] at h
    rw [← mulN_unpackQ, unpackQ_codeQ A h.1, unpackQ_codeQ B h.2]
  · rw [mulN]
    exact List.map_congr_left (fun v _ => mvNR_eq A v)

theorem mulN_toF (A B : List ℕ) : mulN A B = mulNF A B := (mulNF_eq A B).symm

theorem mvN_toR (A : List ℕ) (v : ℕ) : mvN A v = mvNR A v := (mvNR_eq A v).symm

theorem powN_toF (x : List ℕ) : ∀ k, powN 12 x k = powNF x k
  | 0 => rfl
  | k + 1 => by rw [powN, powNF, powN_toF x k, mulN_toF]

theorem sqN_toF (x : List ℕ) : ∀ k, sqN x k = sqNF x k
  | 0 => rfl
  | k + 1 => by rw [sqN, sqNF, sqN_toF x k, mulN_toF]

theorem unpackQ_beq {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144) :
    (unpackQ X == unpackQ Y) = (X == Y) := by
  by_cases h : X = Y
  · subst h
    simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun e => h (unpackQ_inj hX hY e))]

theorem getD_unpackQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true) (i : ℕ) :
    gens.getD i (oneN 12) = unpackQ ((gens.map codeQ).getD i oneQ) := by
  rw [List.all_eq_true] at hg
  by_cases hi : i < gens.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map, unpackQ_codeQ _ (hg _ (List.getElem_mem hi))]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hi),
      oneQ_eq]

def QRel (gens : List (List ℕ))
    (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT ℕ × List ℕ × List ℕ) : Prop :=
  a.2.1.map (evalW 12 gens) = b.2.1.map unpackQ ∧ a.2.2.map Prod.snd = b.2.2.map unpackQ ∧
    (∀ p ∈ a.2.2, p.2 = evalW 12 gens p.1) ∧ (∀ q ∈ b.2.1, q < 2 ^ 144) ∧
    (∀ q ∈ b.2.2, q < 2 ^ 144) ∧ ∀ q, q < 2 ^ 144 → a.1.contains (unpackQ q) = memP b.1 q

def stepHQ (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ) :=
  let y := mulN (gens.getD i (oneN 12)) wx.2
  if st.1.contains y then st else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)

def stepQ (gp : List ℕ) (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (i : ℕ) : NT ℕ × List ℕ × List ℕ :=
  let y := mulQ (gp.getD i oneQ) x
  if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)

theorem stepRelQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true)
    (wx : List ℕ × List ℕ) (x : ℕ) (hwx : wx.2 = evalW 12 gens wx.1) (hx : wx.2 = unpackQ x)
    (i : ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT ℕ × List ℕ × List ℕ) (h : QRel gens a b) :
    QRel gens (stepHQ gens wx a i) (stepQ (gens.map codeQ) x b i) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h2, h3, h4, h5, h6, h1⟩ := h
  dsimp only at h2 h3 h4 h5 h6 h1
  unfold stepHQ stepQ
  dsimp only
  have hy : mulN (gens.getD i (oneN 12)) wx.2 =
      unpackQ (mulQ ((gens.map codeQ).getD i oneQ) x) := by
    rw [getD_unpackQ gens hg i, hx, mulN_unpackQ]
  have hlt := mulQ_lt ((gens.map codeQ).getD i oneQ) x
  have hev : evalW 12 gens (i :: wx.1) = mulN (gens.getD i (oneN 12)) wx.2 := by
    rw [hwx]
    rfl
  rw [hy, h1 _ hlt]
  by_cases hc : memP b1 (mulQ ((gens.map codeQ).getD i oneQ) x) = true
  · rw [if_pos hc, if_pos hc]
    exact ⟨h2, h3, h4, h5, h6, h1⟩
  · rw [if_neg hc, if_neg hc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, h2, hev, hy]
    · simp only [List.map_cons, h3]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (hev.trans hy).symm
      · exact h4 p hp
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hlt
      · exact h5 q hq
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hlt
      · exact h6 q hq
    · intro q hq
      dsimp only
      rw [Std.HashSet.contains_insert, memP_insP, h1 q hq, unpackQ_beq hlt hq]

theorem foldl_innerQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true)
    (wx : List ℕ × List ℕ) (x : ℕ) (hwx : wx.2 = evalW 12 gens wx.1) (hx : wx.2 = unpackQ x) :
    ∀ (l : List ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
      (b : NT ℕ × List ℕ × List ℕ), QRel gens a b →
      QRel gens (l.foldl (stepHQ gens wx) a) (l.foldl (stepQ (gens.map codeQ) x) b)
  | [], _, _, h => h
  | i :: l, a, b, h =>
    foldl_innerQ gens hg wx x hwx hx l _ _ (stepRelQ gens hg wx x hwx hx i a b h)

theorem foldl_outerQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true) :
    ∀ (fr : List (List ℕ × List ℕ)) (frP : List ℕ), fr.map Prod.snd = frP.map unpackQ →
      (∀ p ∈ fr, p.2 = evalW 12 gens p.1) →
      ∀ (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
        (b : NT ℕ × List ℕ × List ℕ), QRel gens a b →
        QRel gens (fr.foldl (fun st wx => (List.range gens.length).foldl (stepHQ gens wx) st) a)
          (frP.foldl (fun st x => (List.range gens.length).foldl
            (stepQ (gens.map codeQ) x) st) b)
  | [], [], _, _, _, _, h => h
  | [], _ :: _, he, _, _, _, _ => by simp at he
  | _ :: _, [], he, _, _, _, _ => by simp at he
  | wx :: fr, x :: frP, he, hfr, a, b, h => by
    simp only [List.map_cons, List.cons.injEq] at he
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_outerQ gens hg fr frP he.2 (fun p hp => hfr p (List.mem_cons_of_mem _ hp)) _ _
      (foldl_innerQ gens hg wx x (hfr wx List.mem_cons_self) he.1 _ a b h)

theorem bfsW_eqQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true) (cap : ℕ) :
    ∀ (fuel : ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
      (b : NT ℕ × List ℕ × List ℕ), QRel gens a b →
      (bfsW 12 gens cap fuel a.1 a.2.1 a.2.2).map (evalW 12 gens) =
        (bfsQ (gens.map codeQ) cap fuel b.1 b.2.1 b.2.2).map unpackQ
  | 0, a, b, h => h.1
  | fuel + 1, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, h => by
    obtain ⟨h2, h3, h4, h5, h6, h1⟩ := h
    dsimp only at h2 h3 h4 h5 h6 h1 ⊢
    have hlen : a2.length = b2.length := by
      have := congrArg List.length h2
      simpa using this
    match a3, b3, h3 with
    | [], [], _ => simp only [bfsW, bfsQ]; exact h2
    | [], _ :: _, he => simp at he
    | _ :: _, [], he => simp at he
    | wx :: fr, x :: frP, he =>
      simp only [bfsW, bfsQ, List.length_map]
      rw [hlen]
      split_ifs with hc
      · exact h2
      · have hrel := foldl_outerQ gens hg (wx :: fr) (x :: frP) he h4 (a1, a2, [])
          (b1, b2, []) ⟨h2, rfl, by simp, h5, by simp, h1⟩
        exact bfsW_eqQ gens hg cap fuel _ _ hrel

theorem elemsOf_eqQ (gens : List (List ℕ)) (hg : gens.all (validB 12) = true) (cap : ℕ) :
    elemsOf 12 gens cap = (elemsQ (gens.map codeQ) cap).map unpackQ := by
  rw [elemsOf, wordsOf, elemsQ]
  refine bfsW_eqQ gens hg cap 400 (((∅ : Std.HashSet (List ℕ)).insert (oneN 12)), [[]],
    [([], oneN 12)]) (insP (.tip []) oneQ, [oneQ], [oneQ]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalW, oneQ_eq]
  · simp [oneQ_eq]
  · simp [evalW]
  · simpa using oneQ_lt
  · simpa using oneQ_lt
  · intro q hq
    dsimp only
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty,
      ← oneQ_eq, unpackQ_beq oneQ_lt hq]

theorem elemsOf_toQ (gens : List (List ℕ)) (cap : ℕ) : elemsOf 12 gens cap = elemsQF gens cap := by
  rw [elemsQF]
  split_ifs with hg
  · have e : validQ = validB 12 := funext validQ_eq
    rw [e] at hg
    exact elemsOf_eqQ gens hg cap
  · rfl

end CFSG.KC.Mat12P

end
