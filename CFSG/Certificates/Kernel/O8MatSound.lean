module

public import Certificates.Data.Kernel.O8.Mat
public import Certificates.Data.Kernel.O8.SA
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.O8.Mat

open CFSG.KC.Enum

theorem foldr_ite_xor (L : List Nat) (f : Nat → Nat) (b : Nat → Bool) :
    L.foldr (fun c acc => if b c then f c ^^^ acc else acc) 0 =
      L.foldr (fun c acc => (if b c then f c else 0) ^^^ acc) 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    simp only [List.foldr_cons, ih]
    cases b c <;> simp

theorem foldr_xor_split (L : List Nat) (f g : Nat → Nat) :
    L.foldr (fun c acc => (f c ^^^ g c) ^^^ acc) 0 =
      L.foldr (fun c acc => f c ^^^ acc) 0 ^^^ L.foldr (fun c acc => g c ^^^ acc) 0 := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.foldr_cons, ih]
    ac_rfl

theorem matApp_eq (M v : Nat) : matApp M v =
    (List.range 8).foldr (fun c acc => (if v.testBit c then M / 256 ^ c % 256 else 0) ^^^ acc)
      0 := by
  rw [matApp, foldr_ite_xor]

theorem matApp_xor (M x y : Nat) : matApp M (x ^^^ y) = matApp M x ^^^ matApp M y := by
  rw [matApp_eq, matApp_eq, matApp_eq, ← foldr_xor_split]
  congr 1
  funext c acc
  rw [Nat.testBit_xor]
  cases x.testBit c <;> cases y.testBit c <;> simp

theorem matApp_zero (M : Nat) : matApp M 0 = 0 := by
  simp [matApp, List.range_succ]

theorem foldr_xor_lt (L : List Nat) (f : Nat → Nat) (hf : ∀ c, f c < 256) :
    L.foldr (fun c acc => f c ^^^ acc) 0 < 256 := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.foldr_cons]
    exact Nat.xor_lt_two_pow (n := 8) (hf c) ih

theorem matApp_lt (M v : Nat) : matApp M v < 256 := by
  rw [matApp_eq]
  refine foldr_xor_lt _ _ fun c => ?_
  split
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem foldr_xor_zero {g : Nat → Nat} :
    ∀ {L : List Nat}, (∀ c ∈ L, g c = 0) → L.foldr (fun c acc => g c ^^^ acc) 0 = 0
  | [], _ => rfl
  | a :: L, h => by
    rw [List.foldr_cons, h a List.mem_cons_self,
      foldr_xor_zero fun c hc => h c (List.mem_cons_of_mem _ hc), Nat.zero_xor]

theorem foldr_xor_single {c : Nat} {g : Nat → Nat} (hg : ∀ c', c' ≠ c → g c' = 0) :
    ∀ {L : List Nat}, L.Nodup → c ∈ L → L.foldr (fun c' acc => g c' ^^^ acc) 0 = g c
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, hn, h => by
    rw [List.foldr_cons]
    obtain ⟨ha, hn⟩ := List.nodup_cons.1 hn
    rcases List.mem_cons.1 h with rfl | h
    · rw [foldr_xor_zero fun c' hc' => hg c' fun e => ha (e ▸ hc'), Nat.xor_zero]
    · rw [hg a fun e => ha (e ▸ h), Nat.zero_xor, foldr_xor_single hg hn h]

theorem matApp_pow (M : Nat) {c : Nat} (hc : c < 8) : matApp M (2 ^ c) = M / 256 ^ c % 256 := by
  rw [matApp_eq]
  refine (foldr_xor_single (g := fun c' => if (2 ^ c).testBit c' then M / 256 ^ c' % 256 else 0)
    (fun c' hc' => ?_) (List.nodup_range) (List.mem_range.2 hc)).trans ?_
  · simp [Ne.symm hc']
  · simp

theorem horner_byte (f : Nat → Nat) (hf : ∀ c, f c < 256) :
    ∀ (n s k : Nat), k < n →
      (List.range' s n).foldr (fun c acc => f c + 256 * acc) 0 / 256 ^ k % 256 = f (s + k)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by
    rw [List.range'_succ, List.foldr_cons, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf s), Nat.add_zero]
  | n + 1, s, k + 1, h => by
    rw [List.range'_succ, List.foldr_cons, pow_succ', ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hf s), Nat.zero_add,
      horner_byte f hf n (s + 1) k (by omega)]
    congr 1
    omega

theorem horner_lt (f : Nat → Nat) (hf : ∀ c, f c < 256) :
    ∀ (n s : Nat), (List.range' s n).foldr (fun c acc => f c + 256 * acc) 0 < 256 ^ n
  | 0, _ => by simp
  | n + 1, s => by
    rw [List.range'_succ, List.foldr_cons, pow_succ']
    have := horner_lt f hf n (s + 1)
    have := hf s
    omega

theorem range8 : List.range 8 = List.range' 0 8 := List.range_eq_range'

theorem matMulM_col (A B : Nat) {k : Nat} (hk : k < 8) :
    matMulM A B / 256 ^ k % 256 = matApp A (B / 256 ^ k % 256) := by
  rw [matMulM, range8, horner_byte _ (fun c => matApp_lt _ _) 8 0 k hk, Nat.zero_add]

theorem matMulM_lt (A B : Nat) : matMulM A B < 2 ^ 64 := by
  rw [matMulM, range8, show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num]
  exact horner_lt _ (fun c => matApp_lt _ _) 8 0

theorem eq_of_bytes : ∀ (n : Nat) {M M' : Nat}, M < 256 ^ n → M' < 256 ^ n →
    (∀ k < n, M / 256 ^ k % 256 = M' / 256 ^ k % 256) → M = M'
  | 0, M, M', hM, hM', _ => by simp at hM hM'; omega
  | n + 1, M, M', hM, hM', h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have ih := eq_of_bytes n (M := M / 256) (M' := M' / 256)
      (by rw [pow_succ'] at hM; omega) (by rw [pow_succ'] at hM'; omega) fun k hk => by
        have := h (k + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.mod_add_div M 256, ← Nat.mod_add_div M' 256, h0, ih]

theorem eq_of_cols {M M' : Nat} (hM : M < 2 ^ 64) (hM' : M' < 2 ^ 64)
    (h : ∀ c < 8, M / 256 ^ c % 256 = M' / 256 ^ c % 256) : M = M' :=
  eq_of_bytes 8 (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by norm_num]; exact hM)
    (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by norm_num]; exact hM') h

theorem matApp_foldr (A : Nat) (L : List Nat) (b : Nat → Bool) (x : Nat → Nat) :
    matApp A (L.foldr (fun c acc => (if b c then x c else 0) ^^^ acc) 0) =
      L.foldr (fun c acc => (if b c then matApp A (x c) else 0) ^^^ acc) 0 := by
  induction L with
  | nil => exact matApp_zero A
  | cons c L ih =>
    simp only [List.foldr_cons]
    rw [matApp_xor, ih]
    cases b c <;> simp [matApp_zero]

theorem foldr_congr_mem {L : List Nat} (f g : Nat → Nat) (h : ∀ c ∈ L, f c = g c) :
    L.foldr (fun c acc => f c ^^^ acc) 0 = L.foldr (fun c acc => g c ^^^ acc) 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.foldr_cons, List.foldr_cons, h c List.mem_cons_self,
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]

theorem matApp_matMulM (A B v : Nat) : matApp (matMulM A B) v = matApp A (matApp B v) := by
  rw [matApp_eq (matMulM A B), matApp_eq B, matApp_foldr]
  exact foldr_congr_mem _ _ fun c hc => by rw [matMulM_col A B (List.mem_range.1 hc)]

theorem matApp_idCode : ∀ v < 256, matApp idCode v = v := by decide +kernel

theorem colK_eq (M c : Nat) : colK M c = M / 256 ^ c % 256 := by
  change (M >>> (8 * c)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem bit_eq (v c : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight v c) 1) 1 = v.testBit c := by
  change ((v >>> c) &&& 1 == 1) = _
  rw [Nat.testBit, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (v >>> c) with h | h <;> simp [h]

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

theorem xor_def (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem matAppK_eq (M v : Nat) : matAppK M v = matApp M v := by
  rw [matApp_eq, range8]
  simp only [matAppK, List.range'_succ, List.range'_zero, List.foldr_cons, List.foldr_nil,
    bit_eq, nIf_eq, colK_eq, xor_def, Nat.zero_add, Nat.reduceAdd, Nat.zero_xor, Nat.xor_zero]
  ac_rfl

@[expose] def horner (d : Nat → Nat) (s n : Nat) : Nat :=
  (List.range' s n).foldr (fun c acc => d c + 256 * acc) 0

theorem horner_succ (d : Nat → Nat) (s n : Nat) :
    horner d s (n + 1) = d s + 256 * horner d (s + 1) n := by
  rw [horner, List.range'_succ, List.foldr_cons]
  rfl

theorem horner_testBit (d : Nat → Nat) (hd : ∀ c, d c < 256) :
    ∀ (n s i : Nat), (horner d s n).testBit i =
      (decide (i < 8 * n) && (d (s + i / 8)).testBit (i % 8))
  | 0, s, i => by simp [horner]
  | n + 1, s, i => by
    rw [horner_succ, Nat.add_comm, show (256 : Nat) = 2 ^ 8 by norm_num,
      Nat.testBit_two_pow_mul_add _ (by simpa using hd s)]
    split
    · next h =>
      have h1 : i / 8 = 0 := Nat.div_eq_of_lt h
      have h2 : i % 8 = i := Nat.mod_eq_of_lt h
      rw [h1, h2, Nat.add_zero]
      simp [show i < 8 * (n + 1) by omega]
    · next h =>
      rw [horner_testBit d hd n (s + 1) (i - 8)]
      have h1 : (i - 8) / 8 + 1 = i / 8 := by omega
      have h2 : (i - 8) % 8 = i % 8 := by omega
      rw [h2, Nat.add_assoc, Nat.add_comm 1, h1]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem horner_lt8 (d : Nat → Nat) (hd : ∀ c, d c < 256) (s : Nat) : horner d s 8 < 2 ^ 64 := by
  have h := horner_lt d hd 8 s
  rw [horner]
  norm_num at h ⊢
  exact h

theorem eq_of_horner_testBit {x : Nat} (d : Nat → Nat) (hd : ∀ c, d c < 256) (hx : x < 2 ^ 64)
    (h : ∀ k < 8, ∀ r < 8, x.testBit (8 * k + r) = (d k).testBit r) : x = horner d 0 8 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [horner_testBit d hd, Nat.zero_add]
  by_cases hi : i < 64
  · have := h (i / 8) (by omega) (i % 8) (Nat.mod_lt _ (by norm_num))
    rw [show 8 * (i / 8) + i % 8 = i by omega] at this
    rw [this]
    simp [show i < 8 * 8 by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [show ¬ i < 8 * 8 by omega]

theorem matMulM_horner (A B : Nat) :
    matMulM A B = horner (fun c => matApp A (B / 256 ^ c % 256)) 0 8 := by
  rw [matMulM, range8]
  rfl

theorem lmask_testBit (i : Nat) :
    (72340172838076673 : Nat).testBit i = (decide (i < 64) && i % 8 == 0) := by
  have e : (72340172838076673 : Nat) = horner (fun _ => 1) 0 8 := by decide
  rw [e, horner_testBit _ (fun _ => by norm_num)]
  rcases Nat.lt_or_ge i 64 with h | h
  · simp only [show i < 8 * 8 by omega, decide_true, Bool.true_and]
    rcases Nat.lt_or_ge (i % 8) 1 with h1 | h1
    · simp [show i % 8 = 0 by omega]
    · rw [Nat.testBit_lt_two_pow (show 1 < 2 ^ (i % 8) from Nat.one_lt_two_pow (by omega))]
      simp [show i % 8 ≠ 0 by omega]
  · simp [show ¬ i < 8 * 8 by omega]

theorem maskMul_eq (A B : Nat) {c : Nat} (hc : c < 8) :
    Nat.land (Nat.shiftRight B c) 72340172838076673 * colK A c =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) 0 8 := by
  have hd : ∀ k, (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) < 256 := by
    intro k
    split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  have hm : Nat.land (Nat.shiftRight B c) 72340172838076673 =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then 1 else 0) 0 8 := by
    refine eq_of_horner_testBit _ (fun k => by split <;> norm_num)
      (lt_of_le_of_lt Nat.and_le_right (by norm_num)) fun k hk r hr => ?_
    change ((B >>> c) &&& 72340172838076673).testBit (8 * k + r) = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, lmask_testBit]
    have e1 : (B / 256 ^ k % 256).testBit c = B.testBit (8 * k + c) := by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow]
      simp [hc, Nat.add_comm]
    rw [e1]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · have h1 : decide (8 * k + 0 < 64) = true := by simp; omega
      have h2 : ((8 * k + 0) % 8 == 0) = true := by simp
      rw [h1, h2, Bool.true_and, Bool.and_true, Nat.add_zero, Nat.add_comm c]
      split <;> simp_all
    · have hne : ((8 * k + r) % 8 == 0) = false := by simp; omega
      have h1 : (1 : Nat).testBit r = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      rw [hne, Bool.and_false, Bool.and_false]
      split <;> simp [h1]
  rw [hm, colK_eq]
  generalize A / 256 ^ c % 256 = a at hd ⊢
  have : ∀ s n, horner (fun k => if (B / 256 ^ k % 256).testBit c then 1 else 0) s n * a =
      horner (fun k => if (B / 256 ^ k % 256).testBit c then a else 0) s n := by
    intro s n
    induction n generalizing s with
    | zero => simp [horner]
    | succ n ih =>
      rw [horner_succ, horner_succ, Nat.add_mul, Nat.mul_assoc, ih]
      congr 1
      split <;> simp
  exact this 0 8

theorem horner_xor (d e : Nat → Nat) (hd : ∀ c, d c < 256) (he : ∀ c, e c < 256) :
    horner d 0 8 ^^^ horner e 0 8 = horner (fun k => d k ^^^ e k) 0 8 := by
  refine eq_of_horner_testBit _ (fun c => Nat.xor_lt_two_pow (n := 8) (hd c) (he c))
    (Nat.xor_lt_two_pow (horner_lt8 d hd 0) (horner_lt8 e he 0)) fun k hk r hr => ?_
  rw [Nat.testBit_xor, horner_testBit d hd, horner_testBit e he, Nat.testBit_xor]
  have h1 : (8 * k + r) / 8 = k := by omega
  have h2 : (8 * k + r) % 8 = r := by omega
  rw [h1, h2, Nat.zero_add]
  simp [show 8 * k + r < 8 * 8 by omega]

theorem matMulK_eq (A B : Nat) : matMulK A B = matMulM A B := by
  have hd : ∀ c < 8, ∀ k, (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) < 256 :=
    fun c _ k => by split <;> [exact Nat.mod_lt _ (by norm_num); norm_num]
  have key : ∀ n ≤ 8, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight B c) (nat_lit 72340172838076673))
        (colK A c))) n =
      horner (fun k => (List.range n).foldr (fun c acc =>
        (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) 0) 0 8 := by
    intro n hn
    induction n with
    | zero =>
      change 0 = _
      rw [horner]
      simp [List.range'_succ]
    | succ n ih =>
      change Nat.xor (Nat.rec (motive := fun _ => Nat) (nat_lit 0) _ n) _ = _
      rw [ih (by omega), Nat.mul_eq, maskMul_eq A B (by omega), xor_def]
      rw [horner_xor _ _ (fun k => foldr_xor_lt _ _ fun c => by
          split <;> [exact Nat.mod_lt _ (by norm_num); norm_num]) (hd n (by omega))]
      congr 1
      funext k
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.xor_zero]
      have : ∀ (L : List Nat) (x : Nat), L.foldr (fun c acc =>
          (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) x =
          L.foldr (fun c acc =>
            (if (B / 256 ^ k % 256).testBit c then A / 256 ^ c % 256 else 0) ^^^ acc) 0 ^^^ x := by
        intro L x
        induction L with
        | nil => simp
        | cons a L ihL => rw [List.foldr_cons, List.foldr_cons, ihL, Nat.xor_assoc]
      conv_rhs => rw [this]
  rw [matMulM_horner, show matMulK A B = Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight B c) (nat_lit 72340172838076673))
        (colK A c))) 8 from rfl, key 8 le_rfl]
  congr 1
  funext k
  rw [matApp_eq]

end CFSG.KC.O8.Mat

end
