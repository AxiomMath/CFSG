module

public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsData

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmul bxor unpackN packN linBits certCheckWith
  injCheckWith testBit_bitsOf xorFold xorFold_succ rowMul testBit_rowMul btr)

private theorem pw2_eqU (w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

private theorem maskN_eqU (w : ℕ) : maskN w = 2 ^ w - 1 := by
  rw [maskN, pw2_eqU]
  rfl

private theorem testBit_fgetU (X i w p : ℕ) :
    (fget X i w).testBit p = (decide (p < w) && X.testBit (i * w + p)) := by
  change ((X >>> (i * w)) &&& maskN w).testBit p = _
  rw [maskN_eqU, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

private theorem bit_eqU (X i : ℕ) : bit X i = X.testBit i := by
  have e : bit X i = Nat.beq ((X >>> i) % 2) 1 := by
    change Nat.beq ((X >>> i) &&& 1) 1 = _
    rw [Nat.and_one_is_mod]
  have h2 : X.testBit i = decide ((X >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, h2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> i) with h | h <;> rw [h] <;> rfl

private theorem testBit_nIfU (c : Bool) (x y t : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) y x c).testBit t = (if c then x.testBit t else y.testBit t) := by
  cases c <;> rfl

private theorem testBit_ltU {x w j : ℕ} (hx : x < 2 ^ w) (hj : w ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))

theorem testBit_packM (d : ℕ) (A : Array ℕ) (p : ℕ) :
    (packM d A).testBit p = (decide (p < d * d) && (A.getD (p / d) 0).testBit (p % d)) := by
  rw [packM, testBit_bitsOf]

private theorem testBit_orN_shift {w : ℕ} {X : ℕ → ℕ} (hX : ∀ i, X i < 2 ^ w) (p : ℕ) : ∀ n,
    (orN n fun i => Nat.shiftLeft (X i) (Nat.mul w i)).testBit p =
      (decide (p < w * n) && (X (p / w)).testBit (p % w))
  | 0 => by
    have e : (orN 0 fun i => Nat.shiftLeft (X i) (Nat.mul w i)) = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : (orN (n + 1) fun i => Nat.shiftLeft (X i) (Nat.mul w i)) =
        (X n <<< (w * n)) ||| (orN n fun i => Nat.shiftLeft (X i) (Nat.mul w i)) := rfl
    rw [e, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_orN_shift hX p n]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      have : X n = 0 := by have := hX n; simp at this; omega
      simp [this]
    by_cases h1 : p < w * n
    · have h2 : p < w * (n + 1) := by rw [Nat.mul_succ]; omega
      have h3 : ¬ p ≥ w * n := by omega
      simp [h1, h2, h3]
    · by_cases h2 : p < w * (n + 1)
      · have e1 : p / w = n := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega)
          (by rw [Nat.succ_mul, Nat.mul_comm]; rw [Nat.mul_succ] at h2; omega)
        have e2 : p % w = p - w * n := by
          have := Nat.div_add_mod p w
          rw [e1] at this
          omega
        have h3 : p ≥ w * n := by omega
        simp [h1, h2, h3, e1, e2]
      · have h4 : (X n).testBit (p - w * n) = false :=
          testBit_ltU (hX n) (by rw [Nat.mul_succ] at h2; omega)
        simp [h1, h2, h4]

theorem packM_lt_proved (d : ℕ) (A : Array ℕ) : packM d A < 2 ^ (d * d) := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  rw [testBit_packM]
  simp
  omega

theorem packM_bxor_proved (d : ℕ) (A B : Array ℕ) :
    packM d (bxor d A B) = Nat.xor (packM d A) (packM d B) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change _ = (packM d A ^^^ packM d B).testBit p
  rw [Nat.testBit_xor, testBit_packM, testBit_packM, testBit_packM]
  by_cases hp : p < d * d
  · have hq : p / d < d := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp at hp
      · exact (Nat.div_lt_iff_lt_mul hd).2 hp
    simp [hp, bxor, Array.getD_eq_getD_getElem?, hq, Nat.testBit_xor]
  · simp [hp]

theorem packM_unpackN_proved (n v s : ℕ) : packM n (unpackN n v s) = fget v s (n * n) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_packM, testBit_fgetU]
  by_cases hp : p < n * n
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp at hp
      · exact hn
    have hq : p / n < n := (Nat.div_lt_iff_lt_mul hn).2 hp
    have hr : p % n < n := Nat.mod_lt _ hn
    simp only [hp, decide_true, Bool.true_and]
    simp only [unpackN, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hq, ↓reduceDIte,
      Option.getD_some, testBit_bitsOf, hr, decide_true, Bool.true_and]
    congr 1
    have := Nat.div_add_mod p n
    calc n * n * s + n * (p / n) + p % n = n * n * s + (n * (p / n) + p % n) := by omega
      _ = s * (n * n) + p := by rw [this, Nat.mul_comm (n * n)]
  · simp [hp]

theorem getD_unpackN_proved {n r : ℕ} (v s : ℕ) (hr : r < n) :
    (unpackN n v s).getD r 0 = fget (fget v s (n * n)) r n := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_fgetU, testBit_fgetU]
  simp only [unpackN, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hr, ↓reduceDIte,
    Option.getD_some, testBit_bitsOf]
  by_cases hp : p < n
  · have h2 : r * n + p < n * n := by
      have : r * n + n ≤ n * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
      omega
    simp only [hp, h2, decide_true, Bool.true_and]
    congr 1
    rw [Nat.mul_comm r n, Nat.mul_comm (n * n) s]
    omega
  · simp [hp]

theorem packN_eq_proved (n k : ℕ) (f : ℕ → Array ℕ) :
    packN n k f = orN k fun s => Nat.shiftLeft (packM n (f s)) (Nat.mul s (n * n)) := by
  have e : (orN k fun s => Nat.shiftLeft (packM n (f s)) (Nat.mul s (n * n))) =
      orN k fun s => Nat.shiftLeft (packM n (f s)) (Nat.mul (n * n) s) := by
    apply orN_congr
    intro s _
    congr 1
    exact Nat.mul_comm _ _
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_orN_shift (fun s => packM_lt_proved n (f s)), packN, testBit_bitsOf, testBit_packM]
  by_cases hp : p < k * (n * n)
  · have hp' : p < n * n * k := by rw [Nat.mul_comm]; exact hp
    have hnn : 0 < n * n := by
      rcases Nat.eq_zero_or_pos (n * n) with h | h
      · rw [h] at hp
        simp at hp
      · exact h
    have hs : p / (n * n) < k := (Nat.div_lt_iff_lt_mul hnn).2 hp
    have hm : p % (n * n) < n * n := Nat.mod_lt _ hnn
    have hn : 0 < n := Nat.pos_of_mul_pos_left hnn
    have e2 : p % (n * n) % n = p % n := Nat.mod_mod_of_dvd _ (Dvd.intro_left n rfl)
    simp [hp, hp', hm, Array.getD_eq_getD_getElem?, hs, e2]
  · have hp' : ¬ p < n * n * k := by rw [Nat.mul_comm]; exact hp
    simp [hp, hp']

private theorem xorFold_congrU {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

private theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  change ((X >>> (i * w)) &&& maskN w) < 2 ^ w
  rw [maskN_eqU]
  have h1 : (X >>> (i * w)) &&& (2 ^ w - 1) ≤ 2 ^ w - 1 := Nat.and_le_right
  have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  omega

private noncomputable def vmAux (d M v : ℕ) (c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => nIf(bit v k, Nat.xor (rowF d M k) acc, acc)) c

private theorem vmAux_lt (d M v : ℕ) : ∀ c, vmAux d M v c < 2 ^ d
  | 0 => Nat.two_pow_pos d
  | c + 1 => by
    change Bool.rec (motive := fun _ => ℕ) (vmAux d M v c)
      (Nat.xor (rowF d M c) (vmAux d M v c)) (bit v c) < 2 ^ d
    cases bit v c
    · exact vmAux_lt d M v c
    · exact Nat.xor_lt_two_pow (fget_lt _ _ _) (vmAux_lt d M v c)

private theorem testBit_vmAux (d M v q : ℕ) : ∀ c,
    (vmAux d M v c).testBit q = xorFold c fun k => bit v k && (rowF d M k).testBit q
  | 0 => by simp [vmAux, xorFold]
  | c + 1 => by
    change (Bool.rec (motive := fun _ => ℕ) (vmAux d M v c)
      (Nat.xor (rowF d M c) (vmAux d M v c)) (bit v c)).testBit q = _
    rw [xorFold_succ, ← testBit_vmAux d M v q c]
    cases bit v c
    · simp
    · change (rowF d M c ^^^ vmAux d M v c).testBit q = _
      rw [Nat.testBit_xor]
      simp [Bool.xor_comm]

private theorem testBit_rowF_packM {d i : ℕ} (A : Array ℕ) (hi : i < d) (q : ℕ) :
    (rowF d (packM d A) i).testBit q = (decide (q < d) && (A.getD i 0).testBit q) := by
  rw [rowF, testBit_fgetU, testBit_packM]
  by_cases hq : q < d
  · have h1 : i * d + q < d * d := by
      have : i * d + d ≤ d * d := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      omega
    have h2 : (i * d + q) / d = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq, Nat.zero_add]
    have h3 : (i * d + q) % d = q := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
    simp [hq, h1, h2, h3]
  · simp [hq]

theorem packM_bmul_proved (d : ℕ) (A B : Array ℕ) :
    packM d (bmul d d A B) = mulF d (packM d A) (packM d B) := by
  unfold mulF
  rw [strictN_eq, strictN_eq]
  have e : (orN d fun i => Nat.shiftLeft (vmF d (packM d B) (rowF d (packM d A) i)) (Nat.mul d i)) =
      orN d fun i => Nat.shiftLeft (vmAux d (packM d B) (rowF d (packM d A) i) d) (Nat.mul d i) :=
    rfl
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_orN_shift (fun i => vmAux_lt _ _ _ d), testBit_packM]
  by_cases hp : p < d * d
  · have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp at hp
      · exact hd
    have hq : p / d < d := (Nat.div_lt_iff_lt_mul hd).2 hp
    have hr : p % d < d := Nat.mod_lt _ hd
    simp only [hp, decide_true, Bool.true_and]
    rw [testBit_vmAux]
    simp only [bmul, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hq, ↓reduceDIte,
      Option.getD_some]
    rw [testBit_rowMul]
    apply xorFold_congrU
    intro l hl
    rw [bit_eqU, testBit_rowF_packM A hq, testBit_rowF_packM B hl]
    simp [hl, hr, Array.getD_eq_getD_getElem?]
  · simp [hp]

private theorem testBit_orN_any (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN_any f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem bit_packM_eq {d i j : ℕ} (A : Array ℕ) (hi : i < d) (hj : j < d) :
    bit (packM d A) (d * j + i) = (A.getD j 0).testBit i := by
  rw [bit_eqU, testBit_packM]
  have h1 : d * j + i < d * d := by
    have : d * j + d ≤ d * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    omega
  have e1 : (d * j + i) / d = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (d * j + i) % d = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  simp [h1, e1, e2]

theorem packM_btr_proved(d : ℕ) (A : Array ℕ) :
    packM d (CFSG.EvenSmallLie.UnitarySix.YamadaPar.btr d d A) = trK d (packM d A) := by
  unfold trK
  rw [strictN_eq]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_packM, testBit_orN_any]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  simp only [testBit_orN_any, List.any_eq_true, List.mem_range, testBit_nIfU, pw2_eqU,
    Nat.testBit_two_pow]
  constructor
  · rintro ⟨hp, hb⟩
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp at hp
      · exact hd
    have hq : p / d < d := (Nat.div_lt_iff_lt_mul hd).2 hp
    have hr : p % d < d := Nat.mod_lt _ hd
    refine ⟨p / d, hq, p % d, hr, ?_⟩
    simp only [btr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hq, ↓reduceDIte,
      Option.getD_some, testBit_bitsOf, hr, decide_true, Bool.true_and] at hb
    simp only [Nat.mul_eq, Nat.add_eq]
    rw [bit_packM_eq A hq hr]
    rw [Array.getD_eq_getD_getElem?, hb]
    simp [Nat.div_add_mod]
  · rintro ⟨i, hi, j, hj, h⟩
    simp only [Nat.mul_eq, Nat.add_eq] at h
    rw [bit_packM_eq A hi hj] at h
    cases hb : (A.getD j 0).testBit i
    · rw [hb] at h
      simp at h
    · rw [hb] at h
      simp only [↓reduceIte, decide_eq_true_eq] at h
      subst h
      have e1 : (d * i + j) / d = i := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
      have e2 : (d * i + j) % d = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      have hlt : d * i + j < d * d := by
        have : d * i + d ≤ d * d := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
        omega
      refine ⟨hlt, ?_⟩
      rw [e1, e2]
      simp only [btr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
        Option.getD_some, testBit_bitsOf, hj, decide_true, Bool.true_and]
      rw [← Array.getD_eq_getD_getElem?]
      exact hb

theorem packM_diag16_proved (B : Array ℕ) :
    packM 16 (CFSG.EvenSmallLie.UnitarySix.YamadaPar.diag16 B) =
      Nat.land (packM 16 B) (packM 16 CFSG.EvenSmallLie.UnitarySix.YamadaPar.id16) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change _ = (packM 16 B &&& packM 16 CFSG.EvenSmallLie.UnitarySix.YamadaPar.id16).testBit p
  rw [Nat.testBit_and, testBit_packM, testBit_packM, testBit_packM]
  by_cases hp : p < 16 * 16
  · have hq : p / 16 < 16 := by omega
    simp [hp, hq, CFSG.EvenSmallLie.UnitarySix.YamadaPar.diag16,
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.id16, Array.getD_eq_getD_getElem?, Nat.testBit_and]
  · simp [hp]

private theorem packM_zero8 : packM 8 CFSG.EvenSmallLie.UnitarySix.YamadaPar.zero8 = 0 := by
  decide

private theorem packM_foldl_msum (mask : ℕ) (f : ℕ → Array ℕ) : ∀ k,
    packM 8 ((List.range k).foldl (fun acc m => if mask.testBit m then bxor 8 acc (f m) else acc)
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.zero8) = msumK k mask fun m => packM 8 (f m)
  | 0 => packM_zero8
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e : msumK (k + 1) mask (fun m => packM 8 (f m)) =
        Bool.rec (motive := fun _ => ℕ) (msumK k mask fun m => packM 8 (f m))
          (Nat.xor (packM 8 (f k)) (msumK k mask fun m => packM 8 (f m))) (bit mask k) := rfl
    rw [e, bit_eqU]
    cases h : mask.testBit k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact packM_foldl_msum mask f k
    · simp only [↓reduceIte]
      rw [packM_bxor_proved, packM_foldl_msum mask f k]
      exact Nat.xor_comm _ _

theorem packM_msum_proved (k mask : ℕ) (f : ℕ → Array ℕ) :
    packM 8 (CFSG.EvenSmallLie.UnitarySix.YamadaPar.msum k mask f) =
      msumK k mask fun m => packM 8 (f m) :=
  packM_foldl_msum mask f k

private theorem fget_lor_lo {P U n : ℕ} (hP : P < 2 ^ n) :
    fget (Nat.lor P (Nat.shiftLeft U n)) 0 n = P := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_fgetU]
  change (decide (q < n) && (P ||| U <<< n).testBit (0 * n + q)) = _
  rw [Nat.zero_mul, Nat.zero_add, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hq : q < n
  · have : ¬ q ≥ n := by omega
    simp [hq, this]
  · simp [hq, testBit_ltU (j := q) hP (by omega)]

private theorem fget_lor_hi {P U n : ℕ} (hP : P < 2 ^ n) (hU : U < 2 ^ n) :
    fget (Nat.lor P (Nat.shiftLeft U n)) 1 n = U := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_fgetU]
  change (decide (q < n) && (P ||| U <<< n).testBit (1 * n + q)) = _
  rw [Nat.one_mul, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ltU hP (by omega)]
  by_cases hq : q < n
  · have e : n + q - n = q := by omega
    simp [hq, e]
  · simp [hq, testBit_ltU (j := q) hU (by omega)]

theorem urPairK_eq_proved {d : ℕ} {I Z : Array ℕ} {gen C : ℕ → Array ℕ} {G CL : List ℕ}
    {w : List ℕ}
    (hG : ∀ s ∈ w, getLD 0 G s = packM d (gen s)) (hC : ∀ s ∈ w, getLD 0 CL s = packM d (C s))
    (hI : packM d I = idF d) (hZ : packM d Z = 0) :
    urPairK d G CL w = Nat.lor (packM d (urPairG d I Z gen C w).1)
      (Nat.shiftLeft (packM d (urPairG d I Z gen C w).2) (Nat.mul d d)) := by
  induction w with
  | nil =>
    have e : urPairK d G CL [] = idF d := rfl
    rw [e, urPairG, hI, hZ]
    change _ = idF d ||| 0 <<< (d * d)
    rw [Nat.zero_shiftLeft, Nat.or_zero]
  | cons s w ih =>
    have ih' := ih (fun t ht => hG t (List.mem_cons_of_mem _ ht))
      (fun t ht => hC t (List.mem_cons_of_mem _ ht))
    have e : urPairK d G CL (s :: w) =
        strictN (urPairK d G CL w) fun X => strictN (getLD 0 G s) fun g =>
          Nat.lor (mulF d g (fget X 0 (Nat.mul d d)))
            (Nat.shiftLeft (Nat.xor (mulF d g (fget X 1 (Nat.mul d d)))
              (mulF d (getLD 0 CL s) (fget X 0 (Nat.mul d d)))) (Nat.mul d d)) := rfl
    rw [e, strictN_eq, strictN_eq, ih', hG s (List.mem_cons_self ..), hC s (List.mem_cons_self ..),
      fget_lor_lo (n := Nat.mul d d) (packM_lt_proved _ _),
      fget_lor_hi (n := Nat.mul d d) (packM_lt_proved _ _) (packM_lt_proved _ _),
      ← packM_bmul_proved, ← packM_bmul_proved, ← packM_bmul_proved, ← packM_bxor_proved]
    rfl

private theorem andB_eqU (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private noncomputable def rowOK (n : ℕ) (B Q : List ℕ) (f e l : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.xor (rowMulK e B) (rowMulK f Q)) (maskN n)) (pw2 l)

private theorem seg_spec (n : ℕ) (B Q : List ℕ) : ∀ (F E : List ℕ) (l : ℕ),
    idRowsSeg n B Q F E l = true →
      F.length = E.length ∧ ∀ j < F.length, rowOK n B Q (F.getD j 0) (E.getD j 0) (l + j) = true
  | [], [], _, _ => ⟨rfl, fun j hj => by simp at hj⟩
  | [], _ :: _, _, h => absurd h (by simp [idRowsSeg])
  | _ :: _, [], _, h => absurd h (by simp [idRowsSeg])
  | f :: F, e :: E, l, h => by
    have e0 : idRowsSeg n B Q (f :: F) (e :: E) l =
        andB (rowOK n B Q f e l) (idRowsSeg n B Q F E (Nat.succ l)) := rfl
    rw [e0, andB_eqU, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := seg_spec n B Q F E (Nat.succ l) h.2
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := h2 j (by simpa using hj)
      simp only [List.getD_cons_succ]
      have e1 : l + (j + 1) = Nat.succ l + j := by omega
      rw [e1]
      exact this

private theorem aux_of (n : ℕ) (B Q : List ℕ) : ∀ (F E : List ℕ) (l : ℕ),
    F.length = E.length → l + F.length = n →
      (∀ j < F.length, rowOK n B Q (F.getD j 0) (E.getD j 0) (l + j) = true) →
        idRowsAux n B Q F E l = true
  | [], [], l, _, hl, _ => by
    have e0 : idRowsAux n B Q [] [] l = andB (Nat.beq l n) true := rfl
    rw [e0, andB_eqU]
    simpa using hl
  | [], _ :: _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, h, _, _ => absurd h (by simp)
  | f :: F, e :: E, l, hlen, hl, hr => by
    have e0 : idRowsAux n B Q (f :: F) (e :: E) l =
        andB (rowOK n B Q f e l) (idRowsAux n B Q F E (Nat.succ l)) := rfl
    rw [e0, andB_eqU, Bool.and_eq_true]
    refine ⟨by simpa using hr 0 (by simp), aux_of n B Q F E (Nat.succ l) (by simpa using hlen)
      (by simp at hl; omega) fun j hj => ?_⟩
    have := hr (j + 1) (by simp; omega)
    simp only [List.getD_cons_succ] at this
    have e1 : l + (j + 1) = Nat.succ l + j := by omega
    rw [← e1]
    exact this

theorem idRowsK_of_segs_proved {n c k : ℕ} (f : ℕ → ℕ) {E B Q : List ℕ} (hn : n = c * k)
    (h : ∀ i < k, idRowsSeg n B Q ((List.range' (c * i) c).map f) ((E.drop (c * i)).take c)
      (c * i) = true) (hE : E.length = n) :
    idRowsK n ((List.range n).map f) E B Q = true := by
  apply aux_of n B Q _ _ 0 (by simp [hE]) (by simp)
  intro j hj
  simp only [List.length_map, List.length_range] at hj
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp at hn
      omega
    · exact hc
  have hi : j / c < k := by
    rw [Nat.div_lt_iff_lt_mul hc]
    rw [hn, Nat.mul_comm] at hj
    exact hj
  have hr : j % c < c := Nat.mod_lt _ hc
  have hj' : c * (j / c) + j % c = j := Nat.div_add_mod j c
  obtain ⟨_, h2⟩ := seg_spec n B Q _ _ _ (h (j / c) hi)
  have := h2 (j % c) (by simpa using hr)
  rw [hj'] at this
  rw [Nat.zero_add]
  have eF : ((List.range' (c * (j / c)) c).map f).getD (j % c) 0 = ((List.range n).map f).getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_range' hr, List.getElem?_range hj]
    simp [hj']
  have eE : ((E.drop (c * (j / c))).take c).getD (j % c) 0 = E.getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hr,
      List.getElem?_drop, hj']
  rw [eF, eE] at this
  exact this

private theorem xorFold_succ' (f : ℕ → Bool) : ∀ k,
    xorFold (k + 1) f = (f 0 ^^ xorFold k fun t => f (t + 1))
  | 0 => by simp [xorFold]
  | k + 1 => by
    rw [xorFold_succ, xorFold_succ' f k, xorFold_succ]
    cases f 0 <;> cases xorFold k (fun t => f (t + 1)) <;> cases f (k + 1) <;> rfl

private noncomputable def rmAux (B : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun b _ ih a acc => strictN (nIf(bit a (nat_lit 0), Nat.xor acc b, acc)) fun acc =>
      ih (Nat.shiftRight a (nat_lit 1)) acc) B

private theorem testBit_rmAux (i : ℕ) : ∀ (B : List ℕ) (a acc : ℕ),
    (rmAux B a acc).testBit i =
      (acc.testBit i ^^ xorFold B.length fun t => a.testBit t && (B.getD t 0).testBit i)
  | [], a, acc => by simp [rmAux, xorFold]
  | b :: B, a, acc => by
    have e : rmAux (b :: B) a acc =
        rmAux B (a >>> 1) (Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc b) (bit a 0)) := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e, testBit_rmAux i B, List.length_cons, xorFold_succ']
    simp only [Nat.testBit_shiftRight, List.getD_cons_succ, List.getD_cons_zero, bit_eqU]
    have e2 : ∀ t, a.testBit (1 + t) = a.testBit (t + 1) := fun t => by rw [Nat.add_comm]
    simp only [e2]
    cases a.testBit 0
    · simp
    · change ((acc ^^^ b).testBit i ^^ _) = _
      rw [Nat.testBit_xor]
      simp

private theorem testBit_rowMulK (a : ℕ) (B : List ℕ) (i : ℕ) :
    (rowMulK a B).testBit i = xorFold B.length fun t => a.testBit t && (B.getD t 0).testBit i := by
  have e : rowMulK a B = rmAux B a 0 := rfl
  rw [e, testBit_rmAux]
  simp

private theorem rowOK_bit {n : ℕ} {B Q : List ℕ} {f e l : ℕ} (h : rowOK n B Q f e l = true)
    {i : ℕ} (hi : i < n) :
    ((rowMulK e B).testBit i ^^ (rowMulK f Q).testBit i) = decide (l = i) := by
  have h' := congrArg (fun x => x.testBit i) (Nat.eq_of_beq_eq_true h)
  change ((rowMulK e B ^^^ rowMulK f Q) &&& maskN n).testBit i = (pw2 l).testBit i at h'
  rw [Nat.testBit_and, maskN_eqU, Nat.testBit_two_pow_sub_one, Nat.testBit_xor, pw2_eqU,
    Nat.testBit_two_pow] at h'
  simpa [hi] using h'

private theorem aux_spec (n : ℕ) (B Q : List ℕ) : ∀ (F E : List ℕ) (l : ℕ),
    idRowsAux n B Q F E l = true →
      F.length = E.length ∧ l + F.length = n ∧
        ∀ j < F.length, rowOK n B Q (F.getD j 0) (E.getD j 0) (l + j) = true
  | [], [], l, h => by
    have e0 : idRowsAux n B Q [] [] l = andB (Nat.beq l n) true := rfl
    rw [e0, andB_eqU] at h
    exact ⟨rfl, by simpa using h, fun j hj => by simp at hj⟩
  | [], e :: E, l, h => by
    have e0 : idRowsAux n B Q [] (e :: E) l = andB (Nat.beq l n) false := rfl
    rw [e0, andB_eqU] at h
    simp at h
  | _ :: _, [], _, h => absurd h (by simp [idRowsAux])
  | f :: F, e :: E, l, h => by
    have e0 : idRowsAux n B Q (f :: F) (e :: E) l =
        andB (rowOK n B Q f e l) (idRowsAux n B Q F E (Nat.succ l)) := rfl
    rw [e0, andB_eqU, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := aux_spec n B Q F E (Nat.succ l) h.2
    refine ⟨by simp [h1], by simp; omega, fun j hj => ?_⟩
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := h3 j (by simpa using hj)
      simp only [List.getD_cons_succ]
      have e1 : l + (j + 1) = Nat.succ l + j := by omega
      rw [e1]
      exact this

theorem idRowsK_bit_proved {n : ℕ} {F E B Q : List ℕ} (h : idRowsK n F E B Q = true) :
    F.length = n ∧ E.length = n ∧ ∀ j < n, ∀ i < n,
      ((xorFold B.length fun t => (E.getD j 0).testBit t && (B.getD t 0).testBit i) ^^
        xorFold Q.length fun t => (F.getD j 0).testBit t && (Q.getD t 0).testBit i) =
        decide (j = i) := by
  obtain ⟨hl1, hl2, hrows⟩ := aux_spec n B Q F E 0 h
  simp only [Nat.zero_add] at hl2 hrows
  refine ⟨hl2, by omega, fun j hj i hi => ?_⟩
  have hr := rowOK_bit (hrows j (by omega)) hi
  rwa [testBit_rowMulK, testBit_rowMulK] at hr

private theorem getD_toList (A : Array ℕ) (t : ℕ) : A.toList.getD t 0 = A.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

private theorem btr_row_bit {n m i j : ℕ} (A : Array ℕ) (hi : i < m) (hj : j < n) :
    ((btr n m A).getD i 0).testBit j = (A.getD j 0).testBit i := by
  simp [btr, Array.getD_eq_getD_getElem?, hi, testBit_bitsOf, hj]

private theorem bmul_row_bit {n k i j : ℕ} (A B : Array ℕ) (hi : i < n) :
    ((bmul n k A B).getD i 0).testBit j =
      xorFold k fun l => (A.getD i 0).testBit l && (B.getD l 0).testBit j := by
  simp only [bmul, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some]
  rw [testBit_rowMul]
  simp only [Array.getD_eq_getD_getElem?]

private theorem linBits_bit {n p t j : ℕ} {Fb : ℕ → ℕ} {F : List ℕ}
    (hF : ∀ l < n, Fb (2 ^ l) = getLD 0 F l) (ht : t < p) (hj : j < n) :
    ((linBits n p Fb).getD t 0).testBit j = (F.getD j 0).testBit t := by
  rw [linBits, btr_row_bit _ ht hj]
  simp [Array.getD_eq_getD_getElem?, hj, hF j hj, getLD_eq_getD]

theorem certCheckWith_of_idRowsK_proved {n m p : ℕ} {Fb : ℕ → ℕ} {Bcols Ecols Qcols : Array ℕ}
    {F B : List ℕ} (hF : ∀ l < n, Fb (2 ^ l) = getLD 0 F l) (hB : Bcols.toList = B)
    (hm : B.length = m) (hp : Qcols.size = p)
    (h : idRowsK n F Ecols.toList B Qcols.toList = true) :
    certCheckWith n m p (linBits n p Fb) Bcols Ecols Qcols = true := by
  obtain ⟨hl1, hl2, hrows⟩ := aux_spec n B Qcols.toList F Ecols.toList 0 h
  simp only [Nat.zero_add] at hl2 hrows
  subst hB
  simp only [certCheckWith, CFSG.EvenSmallLie.UnitarySix.YamadaPar.bIsId, List.all_eq_true,
    List.mem_range, beq_iff_eq]
  intro i hi j hj
  simp only [bxor, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some, Nat.testBit_xor]
  rw [← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?, bmul_row_bit _ _ hi,
    bmul_row_bit _ _ hi]
  have hr := rowOK_bit (hrows j (by omega)) hi
  rw [testBit_rowMulK, testBit_rowMulK, hm, Array.length_toList, hp] at hr
  have e1 : (xorFold m fun l => ((btr m n Bcols).getD i 0).testBit l &&
      ((btr n m Ecols).getD l 0).testBit j) =
      xorFold m fun t => (Ecols.toList.getD j 0).testBit t && (Bcols.toList.getD t 0).testBit i := by
    apply xorFold_congrU
    intro l hl
    rw [btr_row_bit _ hi hl, btr_row_bit _ hl hj, getD_toList, getD_toList, Bool.and_comm]
  have e2 : (xorFold p fun l => ((btr p n Qcols).getD i 0).testBit l &&
      ((linBits n p Fb).getD l 0).testBit j) =
      xorFold p fun t => (F.getD j 0).testBit t && (Qcols.toList.getD t 0).testBit i := by
    apply xorFold_congrU
    intro l hl
    rw [btr_row_bit _ hi hl, linBits_bit hF hl hj, getD_toList Qcols l, Bool.and_comm]
  rw [e1, e2, hr]
  simp [eq_comm]

theorem injCheckWith_of_idRowsK_proved {n p : ℕ} {Fb : ℕ → ℕ} {Qcols : Array ℕ} {F : List ℕ}
    (hF : ∀ l < n, Fb (2 ^ l) = getLD 0 F l) (hp : Qcols.size = p)
    (h : idRowsK n F (List.replicate n 0) [] Qcols.toList = true) :
    injCheckWith n p (linBits n p Fb) Qcols = true := by
  obtain ⟨hl1, hl2, hrows⟩ := aux_spec n [] Qcols.toList F (List.replicate n 0) 0 h
  simp only [Nat.zero_add] at hl2 hrows
  simp only [injCheckWith, CFSG.EvenSmallLie.UnitarySix.YamadaPar.bIsId, List.all_eq_true,
    List.mem_range, beq_iff_eq]
  intro i hi j hj
  rw [bmul_row_bit _ _ hi]
  have hr := rowOK_bit (hrows j (by omega)) hi
  rw [testBit_rowMulK, testBit_rowMulK] at hr
  have hx0 : ∀ g : ℕ → Bool, xorFold ([] : List ℕ).length g = false := fun _ => rfl
  rw [hx0, Bool.false_xor, Array.length_toList, hp] at hr
  have e2 : (xorFold p fun l => ((btr p n Qcols).getD i 0).testBit l &&
      ((linBits n p Fb).getD l 0).testBit j) =
      xorFold p fun t => (F.getD j 0).testBit t && (Qcols.toList.getD t 0).testBit i := by
    apply xorFold_congrU
    intro l hl
    rw [btr_row_bit _ hi hl, linBits_bit hF hl hj, getD_toList Qcols l, Bool.and_comm]
  rw [e2, hr]
  simp [eq_comm]

theorem packN_eq (n k : ℕ) (f : ℕ → Array ℕ) :
    packN n k f = orN k fun s => Nat.shiftLeft (packM n (f s)) (Nat.mul s (n * n)) :=
  by apply packN_eq_proved <;> assumption

theorem packM_unpackN (n v s : ℕ) : packM n (unpackN n v s) = fget v s (n * n) :=
  by apply packM_unpackN_proved <;> assumption

theorem packM_bmul (d : ℕ) (A B : Array ℕ) :
    packM d (bmul d d A B) = mulF d (packM d A) (packM d B) :=
  by apply packM_bmul_proved <;> assumption

theorem packM_bxor (d : ℕ) (A B : Array ℕ) :
    packM d (bxor d A B) = Nat.xor (packM d A) (packM d B) :=
  by apply packM_bxor_proved <;> assumption

theorem packM_lt (d : ℕ) (A : Array ℕ) : packM d A < 2 ^ (d * d) :=
  by apply packM_lt_proved <;> assumption

theorem packM_msum (k mask : ℕ) (f : ℕ → Array ℕ) :
    packM 8 (CFSG.EvenSmallLie.UnitarySix.YamadaPar.msum k mask f) =
      msumK k mask fun m => packM 8 (f m) :=
  by apply packM_msum_proved <;> assumption

theorem packM_btr (d : ℕ) (A : Array ℕ) :
    packM d (CFSG.EvenSmallLie.UnitarySix.YamadaPar.btr d d A) = trK d (packM d A) :=
  by apply packM_btr_proved <;> assumption

theorem packM_diag16 (B : Array ℕ) :
    packM 16 (CFSG.EvenSmallLie.UnitarySix.YamadaPar.diag16 B) =
      Nat.land (packM 16 B) (packM 16 CFSG.EvenSmallLie.UnitarySix.YamadaPar.id16) :=
  by apply packM_diag16_proved <;> assumption

theorem getD_unpackN {n r : ℕ} (v s : ℕ) (hr : r < n) :
    (unpackN n v s).getD r 0 = fget (fget v s (n * n)) r n :=
  by apply getD_unpackN_proved <;> assumption

theorem urPairK_eq {d : ℕ} {I Z : Array ℕ} {gen C : ℕ → Array ℕ} {G CL : List ℕ} {w : List ℕ}
    (hG : ∀ s ∈ w, getLD 0 G s = packM d (gen s)) (hC : ∀ s ∈ w, getLD 0 CL s = packM d (C s))
    (hI : packM d I = idF d) (hZ : packM d Z = 0) :
    urPairK d G CL w = Nat.lor (packM d (urPairG d I Z gen C w).1)
      (Nat.shiftLeft (packM d (urPairG d I Z gen C w).2) (Nat.mul d d)) :=
  by apply urPairK_eq_proved <;> assumption

theorem idRowsK_of_segs {n c k : ℕ} (f : ℕ → ℕ) {E B Q : List ℕ} (hn : n = c * k)
    (h : ∀ i < k, idRowsSeg n B Q ((List.range' (c * i) c).map f) ((E.drop (c * i)).take c)
      (c * i) = true) (hE : E.length = n) :
    idRowsK n ((List.range n).map f) E B Q = true :=
  by apply idRowsK_of_segs_proved <;> assumption

theorem certCheckWith_of_idRowsK {n m p : ℕ} {Fb : ℕ → ℕ} {Bcols Ecols Qcols : Array ℕ}
    {F B : List ℕ} (hF : ∀ l < n, Fb (2 ^ l) = getLD 0 F l) (hB : Bcols.toList = B)
    (hm : B.length = m) (hp : Qcols.size = p)
    (h : idRowsK n F Ecols.toList B Qcols.toList = true) :
    certCheckWith n m p (linBits n p Fb) Bcols Ecols Qcols = true :=
  by apply certCheckWith_of_idRowsK_proved <;> assumption

theorem injCheckWith_of_idRowsK {n p : ℕ} {Fb : ℕ → ℕ} {Qcols : Array ℕ} {F : List ℕ}
    (hF : ∀ l < n, Fb (2 ^ l) = getLD 0 F l) (hp : Qcols.size = p)
    (h : idRowsK n F (List.replicate n 0) [] Qcols.toList = true) :
    injCheckWith n p (linBits n p Fb) Qcols = true :=
  by apply injCheckWith_of_idRowsK_proved <;> assumption

end CFSG.KC.U6F2

end
