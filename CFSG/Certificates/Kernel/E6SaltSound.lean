module

public import Certificates.Data.Kernel.E6Salt

public section

namespace CFSG.KC.E6Salt

open CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits CFSG.KC.Loop
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem saltOf_eq (r : ℕ) : saltOf r = r * 2 ^ 192 + r % (2 ^ 191 - 1) := by
  change r <<< 192 + r % (2 ^ 191 - 1) = _
  rw [Nat.shiftLeft_eq]

theorem saltOf_div (r : ℕ) : saltOf r / 2 ^ 192 = r := by
  have h : r % (2 ^ 191 - 1) < 2 ^ 192 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [saltOf_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt h,
    Nat.zero_add]

theorem xor_split {X Y x y : ℕ} (hx : x < 2 ^ 192) (hy : y < 2 ^ 192) :
    (2 ^ 192 * X + x) ^^^ (2 ^ 192 * Y + y) = 2 ^ 192 * (X ^^^ Y) + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hy)]
  split_ifs <;> rw [Nat.testBit_xor]

theorem testBit_maskS (j : ℕ) :
    maskS.testBit j = if j < 192 then decide (j < 64) else (slots 78).testBit (j - 192) := by
  have h (s : ℕ) : maskOfS s = 2 ^ 192 * s + (2 ^ 64 - 1) := rfl
  rw [maskS, h, Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_sub_one]

theorem spreadS_eq (B q : ℕ) : (B >>> q &&& maskS) =
    2 ^ 192 * (B / 2 ^ 192 / 2 ^ q &&& slots 78) + B >>> q % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.testBit_land, testBit_maskS]
  split_ifs with hj
  · rw [Nat.testBit_mod_two_pow]
    exact Bool.and_comm _ _
  · rw [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
      show j - 192 + q + 192 = q + j by omega]

theorem colS_eq (A q : ℕ) :
    A >>> (192 + 78 * q) % 302231454903657293676544 = col (A / 2 ^ 192) q := by
  rw [col, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

theorem mulSAux_eq (A B : ℕ) : ∀ n, ∃ J < 2 ^ 192,
    mulSAux A B n = 2 ^ 192 * mulAux (A / 2 ^ 192) (B / 2 ^ 192) n + J
  | 0 => ⟨0, by norm_num, rfl⟩
  | n + 1 => by
    obtain ⟨J, hJ, e⟩ := mulSAux_eq A B n
    have h : mulSAux A B (n + 1) = (A >>> (192 + 78 * n) % 302231454903657293676544 *
        (B >>> n &&& maskS)) ^^^ mulSAux A B n := rfl
    have hc := col_lt (A / 2 ^ 192) n
    have hw : col (A / 2 ^ 192) n * (B >>> n % 2 ^ 64) < 2 ^ 192 :=
      lt_of_lt_of_le (Nat.mul_lt_mul'' hc (Nat.mod_lt _ (by norm_num))) (by norm_num)
    refine ⟨_, Nat.xor_lt_two_pow hw hJ, ?_⟩
    rw [mulAux, h, e, colS_eq, spreadS_eq, Nat.mul_add,
      Nat.mul_left_comm (col (A / 2 ^ 192) n) (2 ^ 192), xor_split hw hJ]

theorem mulS_div (A B : ℕ) : mulS A B / 2 ^ 192 = mul (A / 2 ^ 192) (B / 2 ^ 192) := by
  obtain ⟨J, hJ, e⟩ := mulSAux_eq A B 78
  have h : mulS A B = saltOf (mulSAux A B 78 >>> 192) := strictN_eq _ _
  rw [h, saltOf_div, e, Nat.shiftRight_eq_div_pow, Nat.add_comm,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hJ, Nat.zero_add, mul]

theorem col_mod (A : ℕ) {q : ℕ} (hq : q < 78) : col (A % 2 ^ 6084) q = col A q := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 78
  · rw [testBit_col _ _ hp, testBit_col _ _ hp, Nat.testBit_mod_two_pow,
      decide_eq_true (by omega), Bool.true_and]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (col_lt _ _) (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (col_lt _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem spread_mod (B : ℕ) {n : ℕ} (hn : n < 78) :
    (B % 2 ^ 6084 / 2 ^ n &&& slots 78) = (B / 2 ^ n &&& slots 78) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_spread, testBit_spread, Nat.testBit_mod_two_pow]
  by_cases hk : k < 78 * 78 ∧ k % 78 = 0
  · rw [decide_eq_true (by omega : k + n < 6084), Bool.true_and]
  · rcases not_and_or.1 hk with hk | hk
    · simp [hk]
    · simp [hk]

theorem mulAux_mod_left (A B : ℕ) : ∀ n, n ≤ 78 → mulAux (A % 2 ^ 6084) B n = mulAux A B n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [mulAux, mulAux, col_mod A (by omega), mulAux_mod_left A B n (by omega)]

theorem mulAux_mod_right (A B : ℕ) : ∀ n, n ≤ 78 → mulAux A (B % 2 ^ 6084) n = mulAux A B n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [mulAux, mulAux, spread_mod B (by omega), mulAux_mod_right A B n (by omega)]

theorem mul_mod_left (A B : ℕ) : mul (A % 2 ^ 6084) B = mul A B :=
  mulAux_mod_left A B 78 le_rfl

theorem mul_mod_right (A B : ℕ) : mul A (B % 2 ^ 6084) = mul A B :=
  mulAux_mod_right A B 78 le_rfl

theorem mulS_data (A B : ℕ) : dataS (mulS A B) = mul (dataS A) (dataS B) % 2 ^ 6084 := by
  rw [dataS, mulS_div, dataS, dataS, mul_mod_left, mul_mod_right]

set_option exponentiation.threshold 6084 in
theorem eqS_iff (A B : ℕ) : eqS A B = true ↔ dataS A = dataS B := by
  change Nat.beq (A >>> 192 % 2 ^ 6084) (B >>> 192 % 2 ^ 6084) = true ↔ _
  rw [Nat.beq_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rfl

theorem oneS_div : oneS / 2 ^ 192 = oneBits := by
  rw [oneS.eq_1]
  exact saltOf_div oneBits

theorem letS_div (c : ℕ) : letS c / 2 ^ 192 = (letterOfCode c).bits := by
  rw [letS.eq_1]
  exact saltOf_div _

theorem allN_succ (n : ℕ) (f : ℕ → Bool) :
    allN (n + 1) f = Bool.rec false (allN n f) (f n) :=
  rfl

theorem allN_spec {f : ℕ → Bool} : ∀ {n}, allN n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    rw [allN_succ] at h
    cases hb : f n
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact allN_spec h i hi
      · rw [hi]
        exact hb

theorem letOK_spec {LP : ℕ} (h : letOK LP = true) {c : ℕ} (hc : c < 16) :
    letT LP c = letS c :=
  Nat.eq_of_beq_eq_true (allN_spec (f := fun c => Nat.beq (letT LP c) (letS c)) h c hc)

section HasBitsS

variable (K : Type) [Field K]

def HasBitsS (g : adjointGroup Tag.E6 K) (A : ℕ) : Prop :=
  HasBits K g (A / 2 ^ 192)

variable {K}

theorem HasBitsS.mul [CharP K 2] {g h : adjointGroup Tag.E6 K} {A B : ℕ}
    (hg : HasBitsS K g A) (hh : HasBitsS K h B) : HasBitsS K (g * h) (mulS A B) := by
  rw [HasBitsS, mulS_div]
  exact HasBits.mul hg hh

theorem HasBitsS.eq_iff {g h : adjointGroup Tag.E6 K} {A B : ℕ}
    (hg : HasBitsS K g A) (hh : HasBitsS K h B) : g = h ↔ eqS A B = true := by
  rw [HasBits.eq_iff hg hh, eqS_iff]
  rfl

theorem HasBitsS.of_eqS {g : adjointGroup Tag.E6 K} {A B : ℕ} (hg : HasBitsS K g A)
    (e : eqS A B = true) : HasBitsS K g B := by
  rw [eqS_iff] at e
  rw [HasBitsS, HasBits, ← (toEnd_eq_toEnd_iff (K := K) (A / 2 ^ 192) (B / 2 ^ 192)).2 e]
  exact hg

theorem hasBitsS_one : HasBitsS K 1 oneS := by
  rw [HasBitsS, oneS_div]
  exact hasBits_one

theorem hasBitsS_saltOf {g : adjointGroup Tag.E6 K} {r : ℕ} (h : HasBits K g r) :
    HasBitsS K g (saltOf r) := by
  rw [HasBitsS, saltOf_div]
  exact h

theorem HasBitsS.pow [CharP K 2] {g : adjointGroup Tag.E6 K} {A : ℕ} (hg : HasBitsS K g A) :
    ∀ n, HasBitsS K (g ^ n) (powS A n)
  | 0 => by
    rw [pow_zero]
    exact hasBitsS_one
  | n + 1 => by
    rw [pow_succ]
    exact (HasBitsS.pow hg n).mul hg

theorem digit_eq (b W m : ℕ) : digit b W m = W / 2 ^ (b * m) % 2 ^ b := by
  change W >>> (b * m) % 2 ^ b = _
  rw [Nat.shiftRight_eq_div_pow]

theorem wordSAux_succ (LP b W m acc : ℕ) :
    wordSAux LP b W (m + 1) acc = wordSAux LP b W m (mulS (letT LP (W / 2 ^ (b * m) % 2 ^ b)) acc) := by
  change strictN (mulS (letT LP (digit b W m)) acc) (wordSAux LP b W m) = _
  rw [strictN_eq, digit_eq]

theorem hasBitsS_wordSAux [CharP K 2] (f : ℕ → adjointGroup Tag.E6 K) {LP b : ℕ}
    (hL : ∀ c < 2 ^ b, HasBitsS K (f c) (letT LP c)) (W : ℕ) :
    ∀ (m : ℕ) {g : adjointGroup Tag.E6 K} {acc : ℕ},
    HasBitsS K g acc → HasBitsS K (((decW b W m).map f).prod * g) (wordSAux LP b W m acc)
  | 0, g, acc, h => by
    change HasBitsS K (1 * g) acc
    rwa [one_mul]
  | m + 1, g, acc, h => by
    rw [wordSAux_succ]
    have e : ((decW b W (m + 1)).map f).prod * g =
        ((decW b W m).map f).prod * (f (W / 2 ^ (b * m) % 2 ^ b) * g) := by
      rw [decW, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        mul_assoc]
    rw [e]
    exact hasBitsS_wordSAux f hL W m ((hL _ (Nat.mod_lt _ (Nat.two_pow_pos b))).mul h)

theorem hasBitsS_wordS [CharP K 2] (f : ℕ → adjointGroup Tag.E6 K) {LP b : ℕ}
    (hL : ∀ c < 2 ^ b, HasBitsS K (f c) (letT LP c)) (W L : ℕ) :
    HasBitsS K (((decW b W L).map f).prod) (wordS LP b W L) := by
  have h := hasBitsS_wordSAux f hL W L hasBitsS_one
  rw [mul_one] at h
  exact h

variable
    [CharP K 2]

theorem hasBitsS_letS (c : ℕ) : HasBitsS K ((letterOfCode c).elt K) (letS c) := by
  rw [HasBitsS, letS_div]
  exact (letterOfCode c).hasBits

theorem hasBitsS_letT {LP : ℕ} (h : letOK LP = true) {c : ℕ} (hc : c < 16) :
    HasBitsS K ((letterOfCode c).elt K) (letT LP c) := by
  rw [letOK_spec h hc]
  exact hasBitsS_letS c

theorem hasBitsS_wordS_letters {LP : ℕ} (h : letOK LP = true) (W L : ℕ) :
    HasBitsS K (evalG K ((decW 4 W L).map letterOfCode)) (wordS LP 4 W L) := by
  have e : evalG K ((decW 4 W L).map letterOfCode) =
      ((decW 4 W L).map fun c => (letterOfCode c).elt K).prod := by
    rw [evalG, List.map_map]
    rfl
  rw [e]
  exact hasBitsS_wordS _ (fun c hc => hasBitsS_letT h (by simpa using hc)) W L

end HasBitsS

end CFSG.KC.E6Salt

end
