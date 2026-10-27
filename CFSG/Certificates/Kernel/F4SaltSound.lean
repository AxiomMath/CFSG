module

public import Certificates.Data.Kernel.F4Salt

public section

namespace CFSG.KC.F4Salt

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.KC.Loop
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem saltOf_eq (r : ℕ) : saltOf r = r * 2 ^ 128 + r % (2 ^ 127 - 1) := by
  change r <<< 128 + r % (2 ^ 127 - 1) = _
  rw [Nat.shiftLeft_eq]

theorem saltOf_div (r : ℕ) : saltOf r / 2 ^ 128 = r := by
  have h : r % (2 ^ 127 - 1) < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [saltOf_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt h,
    Nat.zero_add]

theorem dataS_saltOf (r : ℕ) : dataS (saltOf r) = r % 2 ^ 2704 := by
  rw [dataS, saltOf_div]

theorem xor_split {X Y x y : ℕ} (hx : x < 2 ^ 128) (hy : y < 2 ^ 128) :
    (2 ^ 128 * X + x) ^^^ (2 ^ 128 * Y + y) = 2 ^ 128 * (X ^^^ Y) + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hy)]
  split_ifs <;> rw [Nat.testBit_xor]

theorem testBit_maskS (j : ℕ) :
    maskS.testBit j = if j < 128 then decide (j < 64) else (slots 52).testBit (j - 128) := by
  have h (s : ℕ) : maskOf s = 2 ^ 128 * s + (2 ^ 64 - 1) := rfl
  rw [maskS, h,Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_sub_one]

theorem spreadS_eq (B q : ℕ) : (B >>> q &&& maskS) =
    2 ^ 128 * (B / 2 ^ 128 / 2 ^ q &&& slots 52) + B >>> q % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.testBit_land, testBit_maskS]
  split_ifs with hj
  · rw [Nat.testBit_mod_two_pow]
    exact Bool.and_comm _ _
  · rw [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
      show j - 128 + q + 128 = q + j by omega]

theorem colS_eq (A q : ℕ) :
    A >>> (128 + 52 * q) % 4503599627370496 = col (A / 2 ^ 128) q := by
  rw [col, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

theorem mulSAux_eq (A B : ℕ) : ∀ n, ∃ J < 2 ^ 128,
    mulSAux A B n = 2 ^ 128 * mulAux (A / 2 ^ 128) (B / 2 ^ 128) n + J
  | 0 => ⟨0, by norm_num, rfl⟩
  | n + 1 => by
    obtain ⟨J, hJ, e⟩ := mulSAux_eq A B n
    have h : mulSAux A B (n + 1) = (A >>> (128 + 52 * n) % 4503599627370496 *
        (B >>> n &&& maskS)) ^^^ mulSAux A B n := rfl
    have hc := col_lt (A / 2 ^ 128) n
    have hw : col (A / 2 ^ 128) n * (B >>> n % 2 ^ 64) < 2 ^ 128 :=
      lt_of_lt_of_le (Nat.mul_lt_mul'' hc (Nat.mod_lt _ (by norm_num))) (by norm_num)
    refine ⟨_, Nat.xor_lt_two_pow hw hJ, ?_⟩
    rw [mulAux, h, e, colS_eq, spreadS_eq, Nat.mul_add,
      Nat.mul_left_comm (col (A / 2 ^ 128) n) (2 ^ 128), xor_split hw hJ]

theorem mulS_div (A B : ℕ) : mulS A B / 2 ^ 128 = mul (A / 2 ^ 128) (B / 2 ^ 128) := by
  obtain ⟨J, hJ, e⟩ := mulSAux_eq A B 52
  have h : mulS A B = saltOf (mulSAux A B 52 >>> 128) := strictN_eq _ _
  rw [h, saltOf_div, e, Nat.shiftRight_eq_div_pow, Nat.add_comm,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hJ, Nat.zero_add, mul]

theorem col_mod (A : ℕ) {q : ℕ} (hq : q < 52) : col (A % 2 ^ 2704) q = col A q := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 52
  · rw [testBit_col _ _ hp, testBit_col _ _ hp, Nat.testBit_mod_two_pow,
      decide_eq_true (by omega), Bool.true_and]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (col_lt _ _) (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (col_lt _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem spread_mod (B : ℕ) {n : ℕ} (hn : n < 52) :
    (B % 2 ^ 2704 / 2 ^ n &&& slots 52) = (B / 2 ^ n &&& slots 52) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_spread, testBit_spread, Nat.testBit_mod_two_pow]
  by_cases hk : k < 52 * 52 ∧ k % 52 = 0
  · rw [decide_eq_true (by omega : k + n < 2704), Bool.true_and]
  · rcases not_and_or.1 hk with hk | hk
    · simp [hk]
    · simp [hk]

theorem mulAux_mod_left (A B : ℕ) : ∀ n, n ≤ 52 → mulAux (A % 2 ^ 2704) B n = mulAux A B n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [mulAux, mulAux, col_mod A (by omega), mulAux_mod_left A B n (by omega)]

theorem mulAux_mod_right (A B : ℕ) : ∀ n, n ≤ 52 → mulAux A (B % 2 ^ 2704) n = mulAux A B n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [mulAux, mulAux, spread_mod B (by omega), mulAux_mod_right A B n (by omega)]

theorem mul_mod_left (A B : ℕ) : mul (A % 2 ^ 2704) B = mul A B :=
  mulAux_mod_left A B 52 le_rfl

theorem mul_mod_right (A B : ℕ) : mul A (B % 2 ^ 2704) = mul A B :=
  mulAux_mod_right A B 52 le_rfl

theorem mulS_data (A B : ℕ) : dataS (mulS A B) = mul (dataS A) (dataS B) % 2 ^ 2704 := by
  rw [dataS, mulS_div, dataS, dataS, mul_mod_left, mul_mod_right]

set_option exponentiation.threshold 2704 in
theorem eqS_iff (A B : ℕ) : eqS A B = true ↔ dataS A = dataS B := by
  change Nat.beq (A >>> 128 % 2 ^ 2704) (B >>> 128 % 2 ^ 2704) = true ↔ _
  rw [Nat.beq_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rfl

theorem oneS_div : oneS / 2 ^ 128 = oneBits :=
  saltOf_div _

theorem letS_div (c : ℕ) : letS c / 2 ^ 128 = (letterOfCode c).bits :=
  saltOf_div _

theorem dataS_letS (c : ℕ) : dataS (letS c) = (letterOfCode c).bits % 2 ^ 2704 := by
  rw [dataS, letS_div]

@[expose] def evalFrom (w : List Letter) (X : ℕ) : ℕ :=
  w.foldr (fun l M => mul l.bits M) X

theorem evalFrom_mod (X : ℕ) : ∀ w : List Letter,
    evalFrom w (X % 2 ^ 2704) % 2 ^ 2704 = evalFrom w X % 2 ^ 2704
  | [] => Nat.mod_mod _ _
  | l :: w => by
    change mul l.bits (evalFrom w (X % 2 ^ 2704)) % 2 ^ 2704 = mul l.bits (evalFrom w X) % 2 ^ 2704
    rw [← mul_mod_right _ (evalFrom w (X % 2 ^ 2704)), evalFrom_mod X w, mul_mod_right]

theorem digit_eq (W m : ℕ) : digit W m = W / 2 ^ (3 * m) % 8 := by
  change W >>> (3 * m) % 8 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem wordSAux_succ (W m acc : ℕ) :
    wordSAux W (m + 1) acc = wordSAux W m (mulS (letS (W / 2 ^ (3 * m) % 8)) acc) := by
  change strictN (mulS (letS (digit W m)) acc) (wordSAux W m) = _
  rw [strictN_eq, digit_eq]

theorem wordSAux_data (W : ℕ) : ∀ m acc, dataS (wordSAux W m acc) =
    evalFrom (wordOfCodes (decW8 W m)) (dataS acc) % 2 ^ 2704
  | 0, acc => by
    change dataS acc = dataS acc % 2 ^ 2704
    rw [dataS, Nat.mod_mod]
  | m + 1, acc => by
    rw [wordSAux_succ, wordSAux_data W m, mulS_data, evalFrom_mod, dataS_letS, mul_mod_left]
    simp only [decW8, wordOfCodes, List.map_append, List.map_cons, List.map_nil, evalFrom,
      List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem wordS_data (W L : ℕ) : dataS (wordS W L) = codeBits (decW8 W L) % 2 ^ 2704 := by
  rw [wordS, wordSAux_data, dataS, oneS_div, evalFrom_mod]
  rfl

section HasBitsS

variable (K : Type) [Field K]

def HasBitsS (g : adjointGroup ReeTag.F4.tag K) (A : ℕ) : Prop :=
  HasBits K g (A / 2 ^ 128)

variable {K}

theorem HasBitsS.mul [CharP K 2] {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ}
    (hg : HasBitsS K g A) (hh : HasBitsS K h B) : HasBitsS K (g * h) (mulS A B) := by
  rw [HasBitsS, mulS_div]
  exact HasBits.mul hg hh

theorem HasBitsS.eq_iff {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ}
    (hg : HasBitsS K g A) (hh : HasBitsS K h B) : g = h ↔ eqS A B = true := by
  rw [HasBits.eq_iff hg hh, eqS_iff]
  rfl

theorem hasBitsS_one : HasBitsS K 1 oneS := by
  rw [HasBitsS, oneS_div]
  exact hasBits_one

theorem hasBitsS_saltOf {g : adjointGroup ReeTag.F4.tag K} {r : ℕ} (h : HasBits K g r) :
    HasBitsS K g (saltOf r) := by
  rw [HasBitsS, saltOf_div]
  exact h

variable
    [CharP K 2]

theorem hasBitsS_letS (c : ℕ) : HasBitsS K ((letterOfCode c).elt K) (letS c) := by
  rw [HasBitsS, letS_div]
  exact (letterOfCode c).hasBits

theorem hasBitsS_wordSAux (W : ℕ) : ∀ (m : ℕ) {g : adjointGroup ReeTag.F4.tag K} {acc : ℕ},
    HasBitsS K g acc → HasBitsS K (evalG K (wordOfCodes (decW8 W m)) * g) (wordSAux W m acc)
  | 0, g, acc, h => by
    change HasBitsS K (1 * g) acc
    rwa [one_mul]
  | m + 1, g, acc, h => by
    rw [wordSAux_succ]
    have e : evalG K (wordOfCodes (decW8 W (m + 1))) * g =
        evalG K (wordOfCodes (decW8 W m)) * ((letterOfCode (W / 2 ^ (3 * m) % 8)).elt K * g) := by
      rw [decW8, wordOfCodes, List.map_append, evalG_append, List.map_singleton, evalG_singleton,
        mul_assoc]
      rfl
    rw [e]
    exact hasBitsS_wordSAux W m ((hasBitsS_letS _).mul h)

theorem hasBitsS_wordS (W L : ℕ) :
    HasBitsS K (evalG K (wordOfCodes (decW8 W L))) (wordS W L) := by
  have h := hasBitsS_wordSAux (K := K) W L hasBitsS_one
  rw [mul_one] at h
  exact h

end HasBitsS

end CFSG.KC.F4Salt

end
