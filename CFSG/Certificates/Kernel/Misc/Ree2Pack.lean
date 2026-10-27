module

public import Certificates.Data.Kernel.Misc.Ree2

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop

theorem sN (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem sB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by cases c <;> rfl

theorem bIf_eq (c : Bool) (t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by cases c <;> rfl

theorem bA {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by cases a <;> simp

theorem bNot {a : Bool} : Bool.rec (motive := fun _ => Bool) true false a = true ↔ a = false := by
  cases a <;> simp

theorem nbeq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem nblt (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · refine (decide_eq_false fun h' => ?_).symm
    have : Nat.blt a b = true := Nat.blt_eq.mpr h'
    rw [h] at this
    exact Bool.false_ne_true this
  · exact (decide_eq_true (Nat.blt_eq.mp h)).symm

theorem nble (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false (Nat.not_le_of_not_ble_eq_true (by rw [h]; simp))).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem loopN_zero (b : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : loopN 0 b f s = s := rfl

theorem loopN_succ (n b : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) :
    loopN (n + 1) b f s = loopN n (b + 1) f (f b s) := by
  change strictN (f b s) (loopN n (b + 1) f) = _
  rw [sN]

theorem loopN_succ' (n b : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) :
    loopN (n + 1) b f s = f (b + n) (loopN n b f s) := by
  induction n generalizing b s with
  | zero => rw [loopN_succ]; rfl
  | succ n ih =>
    rw [loopN_succ, ih, loopN_succ]
    congr 1
    omega

theorem allFrom_succ (n b : ℕ) (f : ℕ → Bool) :
    allFrom (n + 1) b f = Bool.rec (motive := fun _ => Bool) false (allFrom n (b + 1) f) (f b) :=
  rfl

theorem allFrom_iff {n b : ℕ} {f : ℕ → Bool} :
    allFrom n b f = true ↔ ∀ i, b ≤ i → i < b + n → f i = true := by
  induction n generalizing b with
  | zero => exact ⟨fun _ i h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ n ih =>
    rw [allFrom_succ, bA, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi hi'
      rcases Nat.eq_or_lt_of_le hi with rfl | hi
      · exact h1
      · exact h2 i hi (by omega)
    · intro h
      exact ⟨h b le_rfl (by omega), fun i hi hi' => h i (by omega) (by omega)⟩

theorem nthL_eq (q1 : ℕ) : ∀ (l : List ℕ) (k : ℕ), nthL q1 l k = l.getD k q1
  | [], _ => rfl
  | x :: l, 0 => rfl
  | x :: l, k + 1 => by
    change nthL q1 l k = _
    rw [nthL_eq q1 l k]
    simp

theorem lenL_eq : ∀ l : List ℕ, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq l]
    rfl

theorem logsOK_iff {q1 : ℕ} : ∀ {l : List ℕ}, logsOK q1 l = true ↔ ∀ x ∈ l, x ≤ q1
  | [] => by simp [logsOK]
  | x :: l => by
    change Bool.rec (motive := fun _ => Bool) false (logsOK q1 l) (Nat.ble x q1) = true ↔ _
    rw [bA, logsOK_iff, nble]
    simp

theorem testBit_fld (X o w t : ℕ) :
    (Nat.land (Nat.shiftRight X o) (2 ^ w - 1)).testBit t =
      (decide (t < w) && X.testBit (o + t)) := by
  change ((X >>> o) &&& (2 ^ w - 1)).testBit t = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem fld_eq_of_testBit {X o w v : ℕ} (hv : v < 2 ^ w)
    (h : ∀ t < w, X.testBit (o + t) = v.testBit t) :
    Nat.land (Nat.shiftRight X o) (2 ^ w - 1) = v := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_fld]
  by_cases ht : t < w
  · simp [ht, h t ht]
  · have : v.testBit t = false :=
      Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [ht, this]

theorem fld_lt (X o w : ℕ) : Nat.land (Nat.shiftRight X o) (2 ^ w - 1) < 2 ^ w := by
  change (X >>> o) &&& (2 ^ w - 1) < 2 ^ w
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem fld_eq_mod (X o w : ℕ) : Nat.land (Nat.shiftRight X o) (2 ^ w - 1) = X / 2 ^ o % 2 ^ w := by
  change (X >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem n65535 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num

theorem getP_def (M p : ℕ) : getP M p = Nat.land (Nat.shiftRight M (16 * p)) (2 ^ 16 - 1) := rfl

theorem getP_lt (M p : ℕ) : getP M p < 2 ^ 16 := by
  rw [getP_def]
  exact fld_lt _ _ _

theorem getP_eq_of_testBit {M p v : ℕ} (hv : v < 2 ^ 16)
    (h : ∀ t < 16, M.testBit (16 * p + t) = v.testBit t) : getP M p = v := by
  rw [getP_def]
  exact fld_eq_of_testBit hv h

theorem div_mul_add {w s t : ℕ} (hw : 0 < w) (ht : t < w) : (w * s + t) / w = s := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem testBit_or_shift {w s v M b : ℕ} (hw : 0 < w) (hv : v < 2 ^ w) :
    (Nat.lor M (Nat.shiftLeft v (Nat.mul w s))).testBit b =
      (M.testBit b || (decide (b / w = s) && v.testBit (b % w))) := by
  change (M ||| (v <<< (w * s))).testBit b = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  congr 1
  rcases Nat.lt_or_ge b (w * s) with h | h
  · have : b / w ≠ s := by
      intro h'
      have := Nat.div_mul_le_self b w
      rw [h'] at this
      have : s * w = w * s := Nat.mul_comm _ _
      omega
    have hb : ¬ b ≥ w * s := by omega
    simp [this, hb]
  · rcases Nat.lt_or_ge b (w * (s + 1)) with h' | h'
    · have hd : b / w = s := by
        have e : b = w * s + (b - w * s) := by omega
        rw [e, div_mul_add hw (by rw [Nat.mul_succ] at h'; omega)]
      have hm : b % w = b - w * s := by
        have := Nat.div_add_mod b w
        rw [hd] at this
        omega
      simp [hd, hm, h]
    · have hd : b / w ≠ s := by
        intro hd
        have := Nat.lt_div_mul_add (a := b) hw
        rw [hd] at this
        nlinarith
      have : v.testBit (b - w * s) = false :=
        Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by
          have : w * (s + 1) = w * s + w := by ring
          omega)))
      simp [hd, this]

theorem testBit_loopN_or {w : ℕ} (hw : 0 < w) {v : ℕ → ℕ} (hv : ∀ i, v i < 2 ^ w) (b : ℕ) :
    ∀ (n s M : ℕ),
      (loopN n s (fun i M => Nat.lor M (Nat.shiftLeft (v i) (Nat.mul w i))) M).testBit b =
      (M.testBit b || (decide (s ≤ b / w ∧ b / w < s + n) && (v (b / w)).testBit (b % w)))
  | 0, s, M => by simp [loopN_zero]
  | n + 1, s, M => by
    rw [loopN_succ, testBit_loopN_or hw hv b n (s + 1), testBit_or_shift hw (hv s)]
    by_cases h1 : b / w = s
    · rw [← h1]; simp
    · have e1 : decide (b / w = s) = false := decide_eq_false h1
      by_cases h2 : s + 1 ≤ b / w ∧ b / w < s + 1 + n
      · have h3 : s ≤ b / w ∧ b / w < s + (n + 1) := by omega
        rw [e1, decide_eq_true h2, decide_eq_true h3]
        simp
      · have h3 : ¬ (s ≤ b / w ∧ b / w < s + (n + 1)) := by omega
        rw [e1, decide_eq_false h2, decide_eq_false h3]
        simp

theorem fld_loopN_or {w : ℕ} (hw : 0 < w) {v : ℕ → ℕ} (hv : ∀ i, v i < 2 ^ w) {n s p : ℕ}
    (hp1 : s ≤ p) (hp2 : p < s + n) :
    Nat.land (Nat.shiftRight
      (loopN n s (fun i M => Nat.lor M (Nat.shiftLeft (v i) (Nat.mul w i))) 0)
      (w * p)) (2 ^ w - 1) = v p := by
  refine fld_eq_of_testBit (hv p) fun t ht => ?_
  rw [testBit_loopN_or hw hv]
  have hd : (w * p + t) / w = p := div_mul_add hw ht
  have hm : (w * p + t) % w = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  simp [hd, hm, hp1, hp2]

theorem fld_loopN_or_out {w : ℕ} (hw : 0 < w) {v : ℕ → ℕ} (hv : ∀ i, v i < 2 ^ w) {n s p : ℕ}
    (hp : ¬ (s ≤ p ∧ p < s + n)) :
    Nat.land (Nat.shiftRight
      (loopN n s (fun i M => Nat.lor M (Nat.shiftLeft (v i) (Nat.mul w i))) 0)
      (w * p)) (2 ^ w - 1) = 0 := by
  refine fld_eq_of_testBit (by positivity) fun t ht => ?_
  rw [testBit_loopN_or hw hv]
  have hd : (w * p + t) / w = p := div_mul_add hw ht
  simp [hd, hp]

theorem testBit_packL : ∀ {l : List ℕ}, (∀ x ∈ l, x < 2 ^ 16) → ∀ b : ℕ,
    (packL l).testBit b = (l.getD (b / 16) 0).testBit (b % 16)
  | [], _, b => by simp [packL]
  | x :: l, hl, b => by
    change (x ||| (packL l <<< 16)).testBit b = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    have hx : x < 2 ^ 16 := hl x (by simp)
    rcases Nat.lt_or_ge b 16 with h | h
    · have h1 : b / 16 = 0 := Nat.div_eq_of_lt h
      have hb : ¬ b ≥ 16 := by omega
      simp [h1, Nat.mod_eq_of_lt h, hb]
    · have h1 : x.testBit b = false :=
        Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num) h))
      rw [testBit_packL (fun y hy => hl y (by simp [hy])) (b - 16)]
      have h2 : b / 16 = (b - 16) / 16 + 1 := by omega
      have h3 : (b - 16) % 16 = b % 16 := by omega
      simp [h1, h, h2, h3]

theorem getP_packL {l : List ℕ} (hl : ∀ x ∈ l, x < 2 ^ 16) (k : ℕ) :
    getP (packL l) k = l.getD k 0 := by
  have hlt : l.getD k 0 < 2 ^ 16 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : l[k]? with
    | none => simp
    | some a => exact hl a (List.mem_of_getElem? h)
  refine getP_eq_of_testBit hlt fun t ht => ?_
  rw [testBit_packL hl]
  have hd : (16 * k + t) / 16 = k := by omega
  have hm : (16 * k + t) % 16 = t := by omega
  rw [hd, hm]

theorem testBit_setP {M p v : ℕ} (hv : v < 2 ^ 16) (b : ℕ) :
    (setP M p v).testBit b =
      if 16 * p ≤ b ∧ b < 16 * p + 16 then v.testBit (b - 16 * p) else M.testBit b := by
  unfold setP
  rw [sN]
  change (M - (Nat.land (Nat.shiftRight M (16 * p)) 65535) <<< (16 * p) +
    v <<< (16 * p)).testBit b = _
  set o := 16 * p
  have hf : Nat.land (Nat.shiftRight M o) 65535 = M / 2 ^ o % 2 ^ 16 := by
    rw [n65535, fld_eq_mod]
  rw [hf, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have h1 := Nat.mod_add_div M (2 ^ o)
  have h2 := Nat.mod_add_div (M / 2 ^ o) (2 ^ 16)
  set Q := M / 2 ^ o / 2 ^ 16
  have hE : M - M / 2 ^ o % 2 ^ 16 * 2 ^ o + v * 2 ^ o =
      2 ^ o * (2 ^ 16 * Q + v) + M % 2 ^ o := by
    have hM : M = M % 2 ^ o + 2 ^ o * (M / 2 ^ o % 2 ^ 16) + 2 ^ o * (2 ^ 16 * Q) := by
      rw [add_assoc, ← mul_add, h2, h1]
    rw [mul_add, Nat.mul_comm (M / 2 ^ o % 2 ^ 16), Nat.mul_comm v]
    generalize M % 2 ^ o = a at hM ⊢
    generalize 2 ^ o * (M / 2 ^ o % 2 ^ 16) = F at hM ⊢
    generalize 2 ^ o * (2 ^ 16 * Q) = G at hM ⊢
    generalize 2 ^ o * v = V
    omega
  rw [hE, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  rcases Nat.lt_or_ge b o with h | h
  · have hb : ¬ (o ≤ b) := by omega
    simp [h, Nat.testBit_mod_two_pow, hb]
  · rw [ite_eq_right (by omega), Nat.testBit_two_pow_mul_add _ hv]
    rcases Nat.lt_or_ge (b - o) 16 with h' | h'
    · rw [ite_eq_left h', ite_eq_left ⟨h, by omega⟩]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.testBit_div_two_pow,
        Nat.testBit_div_two_pow]
      congr 1
      omega

theorem getP_setP {M p v : ℕ} (hv : v < 2 ^ 16) (p' : ℕ) :
    getP (setP M p v) p' = if p' = p then v else getP M p' := by
  split_ifs with h
  · subst h
    refine getP_eq_of_testBit hv fun t ht => ?_
    rw [testBit_setP hv, ite_eq_left (by omega)]
    congr 1
    omega
  · refine getP_eq_of_testBit (getP_lt _ _) fun t ht => ?_
    rw [testBit_setP hv, ite_eq_right (by omega), getP_def, testBit_fld]
    simp [ht]

end CFSG.KC.Misc.Ree2

end
