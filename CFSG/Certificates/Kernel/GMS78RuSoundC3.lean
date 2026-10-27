module

public import Certificates.Data.Kernel.GMS78Ru
public import CFSG.Certificates.Kernel.GMS78RuGen
public import CFSG.Certificates.Kernel.GMS78RuSoundBase

public section

namespace CFSG.KC.GMS.Snd

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru

@[expose] def bxorN : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, g => (g n ^^ bxorN n g)

theorem testBit_xorN (n : Nat) (f : Nat → Nat) (j : Nat) :
    (xorN n f).testBit j = bxorN n (fun i => (f i).testBit j) := by
  induction n with
  | zero => simp [xorN_zero, bxorN]
  | succ n ih => rw [xorN_succ, Nat.testBit_xor, ih]; rfl

theorem bxorN_congr {n : Nat} {g g' : Nat → Bool} (h : ∀ i < n, g i = g' i) :
    bxorN n g = bxorN n g' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bxorN]
    rw [h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem bxorN_single {n j : Nat} {g : Nat → Bool} (h : ∀ i, i ≠ j → g i = false) :
    bxorN n g = (decide (j < n) && g j) := by
  induction n with
  | zero => simp [bxorN]
  | succ n ih =>
    simp only [bxorN, ih]
    by_cases hj : j = n
    · subst hj; simp
    · rw [h n (Ne.symm hj)]
      have : (j < n + 1) ↔ (j < n) := by omega
      simp [this]

theorem xorN_add (a b : Nat) (g : Nat → Nat) :
    xorN (a + b) g = xorN b (fun i => g (a + i)) ^^^ xorN a g := by
  induction b with
  | zero => simp [xorN_zero]
  | succ b ih => rw [← Nat.add_assoc, xorN_succ, ih, xorN_succ, Nat.xor_assoc]

theorem xorN_mul (m n : Nat) (g : Nat → Nat) :
    xorN (m * n) g = xorN m (fun a => xorN n (fun b => g (n * a + b))) := by
  induction m with
  | zero => simp [xorN_zero]
  | succ m ih => rw [Nat.succ_mul, xorN_add, ih, xorN_succ, Nat.mul_comm m n]

theorem xorN_swap (m n : Nat) (f : Nat → Nat → Nat) :
    xorN m (fun a => xorN n (fun b => f a b)) = xorN n (fun b => xorN m (fun a => f a b)) := by
  induction m with
  | zero =>
    simp only [xorN_zero]
    induction n with
    | zero => rfl
    | succ n ih => rw [xorN_succ, ← ih, Nat.xor_zero]
  | succ m ih => rw [xorN_succ, ih, ← xorN_xor]; rfl

theorem xorN_zero_fun (n : Nat) : xorN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorN_succ, ih, Nat.xor_zero]

theorem xorN_cut {n k : Nat} {f : Nat → Nat} (hk : k ≤ n) (h : ∀ i, k ≤ i → i < n → f i = 0) :
    xorN n f = xorN k f := by
  induction n with
  | zero => rw [Nat.le_zero.mp hk]
  | succ n ih =>
    rcases Nat.lt_or_ge n k with h1 | h1
    · have : k = n + 1 := by omega
      rw [this]
    · rw [xorN_succ, h n h1 (Nat.lt_succ_self n), Nat.zero_xor]
      exact ih h1 fun i hi1 hi2 => h i hi1 (Nat.lt_succ_of_lt hi2)

theorem xorN_bits (w n : Nat) :
    xorN n (fun a => if w.testBit a then 2 ^ a else 0) = w % 2 ^ n := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_xorN, Nat.testBit_mod_two_pow]
  rw [bxorN_single (j := j)]
  · split <;> simp_all
  · intro i hij
    split
    · rw [Nat.testBit_two_pow]; simpa using hij
    · simp

theorem decomp {N : Nat} {f : Nat → Nat} (h0 : f 0 = 0)
    (hadd : ∀ a b, a < 2 ^ N → b < 2 ^ N → f (a ^^^ b) = f a ^^^ f b) {w : Nat} (hw : w < 2 ^ N) :
    f w = xorN N (fun a => if w.testBit a then f (2 ^ a) else 0) := by
  have key : ∀ n ≤ N, f (w % 2 ^ n) = xorN n (fun a => if w.testBit a then f (2 ^ a) else 0) := by
    intro n hn
    induction n with
    | zero => simp only [Nat.pow_zero, Nat.mod_one, h0, xorN_zero]
    | succ n ih =>
      have hsplit : w % 2 ^ (n + 1) = w % 2 ^ n ^^^ (if w.testBit n then 2 ^ n else 0) := by
        rw [← xorN_bits, ← xorN_bits, xorN_succ, Nat.xor_comm]
      have hlt1 : w % 2 ^ n < 2 ^ N :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hlt2 : (if w.testBit n then 2 ^ n else 0) < 2 ^ N := by
        split
        · exact Nat.pow_lt_pow_right (by omega) (by omega)
        · exact Nat.two_pow_pos N
      rw [hsplit, hadd _ _ hlt1 hlt2, ih (by omega), xorN_succ, Nat.xor_comm]
      congr 1
      split <;> simp [h0]
  have := key N (Nat.le_refl N)
  rwa [Nat.mod_eq_of_lt hw] at this

theorem orN_field {n w : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ w) {i : Nat} (hi : i < n) :
    fget (orN n (fun i => f i <<< (w * i))) i w = f i := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_fget]
  by_cases hj : j < w
  · simp only [hj, decide_true, Bool.true_and]
    rw [Bool.eq_iff_iff, orN_testBit]
    constructor
    · rintro ⟨i', hi', h⟩
      rw [Nat.testBit_shiftLeft] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases Nat.lt_trichotomy i' i with h1 | h1 | h1
      · exfalso
        have h3 : w * i' + w ≤ i * w := by
          rw [Nat.mul_comm i w, ← Nat.mul_succ]; exact Nat.mul_le_mul_left w h1
        have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf i' hi')
          (Nat.pow_le_pow_right (by omega) (by omega : w ≤ i * w + j - w * i')))
        rw [this] at h; exact absurd h.2 (by decide)
      · subst h1
        rw [Nat.mul_comm i' w, Nat.add_sub_cancel_left] at h
        exact h.2
      · exfalso
        have h3 : w * i + w ≤ w * i' := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left w h1
        rw [Nat.mul_comm i w] at h
        omega
    · intro h
      refine ⟨i, hi, ?_⟩
      rw [Nat.testBit_shiftLeft, Nat.mul_comm i w]
      simp [h]
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf i hi)
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem orN_field_lt {n w : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ w) :
    orN n (fun i => f i <<< (w * i)) < 2 ^ (w * n) := by
  apply orN_lt
  intro i hi
  rw [Nat.shiftLeft_eq]
  calc f i * 2 ^ (w * i) < 2 ^ w * 2 ^ (w * i) :=
        Nat.mul_lt_mul_of_pos_right (hf i hi) (Nat.two_pow_pos _)
    _ = 2 ^ (w * (i + 1)) := by rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    _ ≤ 2 ^ (w * n) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left w hi)

theorem fget_fget_mul {X a k w t : Nat} (ht : t < k) :
    fget (fget X a (k * w)) t w = fget X (k * a + t) w := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [testBit_fget]
  by_cases hj : j < w
  · have : t * w + j < k * w := by
      have := Nat.mul_le_mul_right w (by omega : t + 1 ≤ k)
      rw [Nat.succ_mul] at this; omega
    simp only [hj, this, decide_true, Bool.true_and]
    congr 1
    rw [Nat.add_mul, Nat.mul_comm k a, Nat.mul_assoc, Nat.add_assoc]
  · simp [hj]

theorem sqK_congr {c e v v' : Nat} (h0 : fget v 0 3 = fget v' 0 3) (h1 : fget v 1 3 = fget v' 1 3)
    (h2 : fget v 2 3 = fget v' 2 3) : sqK c e v = sqK c e v' := by
  rw [sqK_eq, sqK_eq, h0, h1, h2]

theorem commK_congr {c x x' z z' : Nat} (h0 : fget x 0 3 = fget x' 0 3)
    (h1 : fget x 1 3 = fget x' 1 3) (h2 : fget x 2 3 = fget x' 2 3) (k0 : fget z 0 3 = fget z' 0 3)
    (k1 : fget z 1 3 = fget z' 1 3) (k2 : fget z 2 3 = fget z' 2 3) :
    commK c x z = commK c x' z' := by
  rw [commK_eq, commK_eq, h0, h1, h2, k0, k1, k2]

theorem xor_lt256 {i j : Nat} (hi : i < 256) (hj : j < 256) : i ^^^ j < 256 :=
  Nat.xor_lt_two_pow (n := 8) hi hj

structure Par (c e p q : Nat) : Prop where
  hc : c < 8
  he : e < 8
  hp : p < 8
  hq : q < 8
  L : MulLaws

@[expose] noncomputable def Qi (c e p q i : Nat) : Nat := sqK c e (wK p q i)

@[expose] noncomputable def Bi (c p q i j : Nat) : Nat := commK c (wK p q i) (wK p q j)

theorem Qi_lt (c e p q i : Nat) : Qi c e p q i < 8 := sqK_lt _ _ _
theorem Bi_lt (c p q i j : Nat) : Bi c p q i j < 8 := commK_lt _ _ _

namespace Par

variable {c e p q : Nat} (P : Par c e p q)
include P

theorem wK_comp_xor {i j : Nat} (hi : i < 256) (hj : j < 256) :
    fget (wK p q (i ^^^ j)) 0 3 = fget (wK p q i ^^^ wK p q j) 0 3 ∧
      fget (wK p q (i ^^^ j)) 1 3 = fget (wK p q i ^^^ wK p q j) 1 3 ∧
      fget (wK p q (i ^^^ j)) 2 3 = fget (wK p q i ^^^ wK p q j) 2 3 := by
  have hij := xor_lt256 hi hj
  simp only [fget_xor, fget_wK0 P.hp P.hq hi, fget_wK0 P.hp P.hq hj, fget_wK0 P.hp P.hq hij,
    fget_wK1 P.hp P.hq hi, fget_wK1 P.hp P.hq hj, fget_wK1 P.hp P.hq hij,
    fget_wK2 P.hp P.hq hi, fget_wK2 P.hp P.hq hj, fget_wK2 P.hp P.hq hij]
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.xor_div_two_pow (n := 5)
  · rw [Nat.xor_div_two_pow (n := 2)]; exact Nat.xor_mod_two_pow (n := 3)
  · rw [Nat.xor_mod_two_pow (n := 2), lamK_xor]

theorem wK_comp_zero :
    fget (wK p q 0) 0 3 = fget 0 0 3 ∧ fget (wK p q 0) 1 3 = fget 0 1 3 ∧
      fget (wK p q 0) 2 3 = fget 0 2 3 := by
  simp only [fget_wK0 P.hp P.hq (by omega : 0 < 256), fget_wK1 P.hp P.hq (by omega : 0 < 256),
    fget_wK2 P.hp P.hq (by omega : 0 < 256), fget_zero]
  simp [lamK_eq]

theorem Qi_xor {i j : Nat} (hi : i < 256) (hj : j < 256) :
    Qi c e p q (i ^^^ j) = Qi c e p q i ^^^ Qi c e p q j ^^^ Bi c p q i j := by
  obtain ⟨h0, h1, h2⟩ := P.wK_comp_xor hi hj
  rw [Qi, sqK_congr h0 h1 h2, P.L.sqK_xor P.hc P.he]; rfl

theorem Qi_zero : Qi c e p q 0 = 0 := by
  obtain ⟨h0, h1, h2⟩ := P.wK_comp_zero
  rw [Qi, sqK_congr h0 h1 h2, P.L.sqK_zero P.hc P.he]

theorem Bi_xor_left {i j k : Nat} (hi : i < 256) (hj : j < 256) :
    Bi c p q (i ^^^ j) k = Bi c p q i k ^^^ Bi c p q j k := by
  obtain ⟨h0, h1, h2⟩ := P.wK_comp_xor hi hj
  rw [Bi, commK_congr h0 h1 h2 rfl rfl rfl, P.L.commK_xor P.hc]; rfl

theorem Bi_symm (i j : Nat) : Bi c p q i j = Bi c p q j i := P.L.commK_symm _ _ _

theorem Bi_xor_right {i j k : Nat} (hj : j < 256) (hk : k < 256) :
    Bi c p q i (j ^^^ k) = Bi c p q i j ^^^ Bi c p q i k := by
  rw [P.Bi_symm, P.Bi_xor_left hj hk, P.Bi_symm j, P.Bi_symm k]

theorem Bi_self (i : Nat) : Bi c p q i i = 0 := P.L.commK_self P.hc _

theorem Bi_zero_left (j : Nat) : Bi c p q 0 j = 0 := by
  obtain ⟨h0, h1, h2⟩ := P.wK_comp_zero
  rw [Bi, commK_congr h0 h1 h2 rfl rfl rfl, P.L.commK_zero P.hc]

theorem Bi_zero_right (i : Nat) : Bi c p q i 0 = 0 := by
  rw [P.Bi_symm, P.Bi_zero_left]

theorem Bi_decomp_right (i : Nat) {w : Nat} (hw : w < 256) :
    Bi c p q i w = xorN 8 (fun b => if w.testBit b then Bi c p q i (2 ^ b) else 0) :=
  decomp (N := 8) (f := Bi c p q i) (P.Bi_zero_right i) (fun _ _ ha hb => P.Bi_xor_right ha hb) hw

theorem Bi_decomp_left (j : Nat) {w : Nat} (hw : w < 256) :
    Bi c p q w j = xorN 8 (fun a => if w.testBit a then Bi c p q (2 ^ a) j else 0) :=
  decomp (N := 8) (f := fun x => Bi c p q x j) (P.Bi_zero_left j)
    (fun _ _ ha hb => P.Bi_xor_left ha hb) hw

end Par

theorem ALL_eq : ALL = 2 ^ 256 - 1 := by rw [ALL, maskN_eq]

theorem testBit_ALL_xor {X x : Nat} (hx : x < 256) : (ALL ^^^ X).testBit x = !X.testBit x := by
  rw [Nat.testBit_xor, ALL_eq, Nat.testBit_two_pow_sub_one]; simp [hx]

theorem ALL_xor_lt {X : Nat} (hX : X < 2 ^ 256) : ALL ^^^ X < 2 ^ 256 := by
  rw [ALL_eq]; exact Nat.xor_lt_two_pow (by omega) hX

theorem testBit_bmK (b x : Nat) : (bmK b).testBit x = (decide (x < 256) && x.testBit b) := by
  unfold bmK
  rw [Bool.eq_iff_iff, orN_testBit]
  simp only [nIf_eq, bit_eq, pw2_eq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, h⟩
    split at h
    · rw [Nat.testBit_two_pow] at h
      have : w = x := by simpa using h
      subst this; exact ⟨hw, by assumption⟩
    · simp at h
  · rintro ⟨hx, h⟩
    exact ⟨x, hx, by simp [h]⟩

theorem bmK_lt (b : Nat) : bmK b < 2 ^ 256 := by
  unfold bmK
  apply orN_lt
  intro w hw
  rw [nIf_eq, pw2_eq]
  split
  · exact Nat.pow_lt_pow_right (by omega) hw
  · exact Nat.two_pow_pos _

theorem BM_field {b : Nat} (hb : b < 8) : fget BM b 256 = bmK b := by
  have : BM = orN 8 (fun b => bmK b <<< (256 * b)) := rfl
  rw [this, orN_field (fun i _ => bmK_lt i) hb]

theorem gAB_eq (c p q a b : Nat) : gAB c p q a b = Bi c p q (2 ^ a) (2 ^ b) := by
  rw [gAB, pw2_eq, pw2_eq]; rfl

@[expose] noncomputable def maF (c p q ix : Nat) : Nat :=
  xorN 8 fun b => if (gAB c p q (ix / 3) b).testBit (ix % 3) then bmK b else 0

theorem maF_lt (c p q ix : Nat) : maF c p q ix < 2 ^ 256 := by
  apply xorN_lt; intro b _; split
  · exact bmK_lt b
  · exact Nat.two_pow_pos _

theorem maK_eq (c p q : Nat) : maK c p q = orN 24 (fun ix => maF c p q ix <<< (256 * ix)) := by
  unfold maK maF
  simp only [nIf_eq, bit_eq, nat_div_eq, nat_mod_eq, nat_mul_eq, nat_shiftLeft_eq]

set_option exponentiation.threshold 1024 in
theorem xwK_lt (MA w : Nat) : xwK MA w < 2 ^ 768 := by
  apply xorN_lt; intro a _
  rw [nIf_eq]; split
  · exact fget_lt _ _ _
  · exact Nat.two_pow_pos _

theorem maK_field (c p q : Nat) {ix : Nat} (hix : ix < 24) :
    fget (maK c p q) ix 256 = maF c p q ix := by
  rw [maK_eq, orN_field (fun i _ => maF_lt c p q i) hix]

namespace Par

variable {c e p q : Nat} (P : Par c e p q)
include P

theorem testBit_maF {a t w : Nat} (ht : t < 3) (hw : w < 256) :
    (maF c p q (3 * a + t)).testBit w = (Bi c p q (2 ^ a) w).testBit t := by
  have h1 : (3 * a + t) / 3 = a := by omega
  have h2 : (3 * a + t) % 3 = t := by omega
  rw [maF, h1, h2, testBit_xorN, P.Bi_decomp_right _ hw, testBit_xorN]
  apply bxorN_congr
  intro b _
  rw [gAB_eq]
  split <;> split <;> simp_all [testBit_bmK]

theorem testBit_xwK {w w' t : Nat} (hw : w < 256) (hw' : w' < 256) (ht : t < 3) :
    (fget (xwK (maK c p q) w) t 256).testBit w' = (Bi c p q w w').testBit t := by
  have hmap : fget (xwK (maK c p q) w) t 256 =
      xorN 8 (fun a => fget (if w.testBit a then fget (maK c p q) a 768 else 0) t 256) := by
    unfold xwK
    simp only [nIf_eq, bit_eq]
    exact xorN_map (fun X => fget X t 256) (fget_zero t 256) (fun a b => fget_xor a b t 256)
  rw [hmap, testBit_xorN, P.Bi_decomp_left _ hw, testBit_xorN]
  apply bxorN_congr
  intro a ha
  split
  · have e768 : (768 : Nat) = 3 * 256 := rfl
    rw [e768, fget_fget_mul ht, maK_field c p q (by omega),
      P.testBit_maF ht hw']
  · simp [fget_zero]

theorem radK_spec {d : Nat} (hd : d < 256) (h : (radK (maK c p q)).testBit d = true) :
    ∀ a < 8, Bi c p q (2 ^ a) d = 0 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) ALL
      (fun i ih => Nat.land ih (Nat.xor ALL (fget (maK c p q) i (nat_lit 256)))) n).testBit d =
        true → ∀ i < n, (fget (maK c p q) i 256).testBit d = false := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro hn i hi
      change (Nat.land _ (Nat.xor ALL _)).testBit d = true at hn
      rw [nat_land_eq, nat_xor_eq, Nat.testBit_and, testBit_ALL_xor hd, Bool.and_eq_true] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih hn.1 i hi
      · simpa using hn.2
  intro a ha
  have hz : ∀ t < 3, (Bi c p q (2 ^ a) d).testBit t = false := by
    intro t ht
    have := key 24 h (3 * a + t) (by omega)
    rw [maK_field c p q (by omega), P.testBit_maF ht hd] at this
    exact this
  apply Nat.eq_of_testBit_eq; intro t
  rcases Nat.lt_or_ge t 3 with ht | ht
  · rw [hz t ht, Nat.zero_testBit]
  · rw [Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Bi_lt c p q _ _)
      (Nat.pow_le_pow_right (n := 2) (by omega) ht : 2 ^ 3 ≤ 2 ^ t))

end Par

theorem lt8_testBit {a : Nat} (ha : a < 8) {t : Nat} (ht : 3 ≤ t) : a.testBit t = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (n := 2) (by omega) ht :
    2 ^ 3 ≤ 2 ^ t))

theorem eq_of_low3 {a b : Nat} (ha : a < 8) (hb : b < 8) (h : ∀ t < 3, a.testBit t = b.testBit t) :
    a = b := by
  apply Nat.eq_of_testBit_eq; intro t
  rcases Nat.lt_or_ge t 3 with ht | ht
  · exact h t ht
  · rw [lt8_testBit ha ht, lt8_testBit hb ht]

theorem gtK_field (c p q : Nat) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    fget (gtK c p q) (8 * a + b) 3 = Bi c p q (2 ^ a) (2 ^ b) := by
  have : gtK c p q = orN 64 (fun ab => gAB c p q (ab / 8) (ab % 8) <<< (3 * ab)) := rfl
  rw [this, orN_field (fun i _ => commK_lt _ _ _) (by omega), gAB_eq]
  congr 2 <;> omega

theorem ttK_field (c p q : Nat) {j k : Nat} (hj : j < 8) (hk : k < 8) :
    fget (ttK c p q) (8 * j + k) 3 = Bi c p q (2 ^ abit j) (2 ^ abit k) := by
  have : ttK c p q = orN 64 (fun jk => gAB c p q (abit (jk / 8)) (abit (jk % 8)) <<< (3 * jk)) :=
    rfl
  rw [this, orN_field (fun i _ => commK_lt _ _ _) (by omega), gAB_eq]
  congr 3 <;> omega

namespace Par

variable {c e p q : Nat} (P : Par c e p q)
include P

theorem Qi_expand {w : Nat} (hw : w < 256) :
    Qi c e p q w = xorN 8 (fun a => if w.testBit a then Qi c e p q (2 ^ a) else 0) ^^^
      xorN 64 (fun ab => if ab / 8 < ab % 8 ∧ w.testBit (ab / 8) = true ∧ w.testBit (ab % 8) = true
        then Bi c p q (2 ^ (ab / 8)) (2 ^ (ab % 8)) else 0) := by
  have step : ∀ n ≤ 8, Qi c e p q (w % 2 ^ n) =
      xorN n (fun a => if w.testBit a then Qi c e p q (2 ^ a) else 0) ^^^
      xorN n (fun b => if w.testBit b then
        xorN b (fun a => if w.testBit a then Bi c p q (2 ^ a) (2 ^ b) else 0) else 0) := by
    intro n hn
    induction n with
    | zero => simp only [Nat.pow_zero, Nat.mod_one, P.Qi_zero, xorN_zero, Nat.xor_zero]
    | succ n ih =>
      have hx : w % 2 ^ n < 256 :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
          (Nat.pow_le_pow_right (n := 2) (by omega) (by omega) : 2 ^ n ≤ 2 ^ 8)
      have h2n : 2 ^ n < 256 := Nat.pow_lt_pow_right (a := 2) (by omega) (by omega : n < 8)
      have hsplit : w % 2 ^ (n + 1) = w % 2 ^ n ^^^ (if w.testBit n then 2 ^ n else 0) := by
        rw [← xorN_bits, ← xorN_bits, xorN_succ, Nat.xor_comm]
      rw [hsplit, xorN_succ, xorN_succ]
      by_cases hb : w.testBit n
      · simp only [hb, ↓reduceIte]
        have hB : Bi c p q (w % 2 ^ n) (2 ^ n) =
            xorN n (fun a => if w.testBit a then Bi c p q (2 ^ a) (2 ^ n) else 0) := by
          rw [P.Bi_decomp_left _ hx]
          rw [xorN_cut (n := 8) (k := n) (by omega) (fun a ha1 _ => by
            rw [Nat.testBit_mod_two_pow]; simp; omega)]
          apply xorN_congr
          intro a ha
          rw [Nat.testBit_mod_two_pow]; simp [ha]
        rw [P.Qi_xor hx h2n, ih (by omega), hB]
        xsimp
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.xor_zero, Nat.zero_xor]
        exact ih (by omega)
  have h8 := step 8 (Nat.le_refl 8)
  rw [Nat.mod_eq_of_lt (by omega : w < 2 ^ 8)] at h8
  rw [h8]
  congr 1
  have hrow : ∀ b < 8, (if w.testBit b then
        xorN b (fun a => if w.testBit a then Bi c p q (2 ^ a) (2 ^ b) else 0) else 0) =
      xorN 8 (fun a => if a < b ∧ w.testBit a = true ∧ w.testBit b = true then
        Bi c p q (2 ^ a) (2 ^ b) else 0) := by
    intro b hb
    rw [xorN_cut (n := 8) (k := b) (f := fun a => if a < b ∧ w.testBit a = true ∧
      w.testBit b = true then Bi c p q (2 ^ a) (2 ^ b) else 0) (by omega)
      (fun a ha _ => by simp; omega)]
    by_cases hwb : w.testBit b
    · simp only [hwb, ↓reduceIte]
      apply xorN_congr; intro a ha; simp [ha]
    · simp only [hwb, Bool.false_eq_true, ↓reduceIte, and_false]
      exact (xorN_zero_fun b).symm
  have e64 : (64 : Nat) = 8 * 8 := rfl
  rw [xorN_congr hrow, xorN_swap, e64, xorN_mul]
  apply xorN_congr; intro a ha
  apply xorN_congr; intro b hb
  have h1 : (8 * a + b) / 8 = a := by omega
  have h2 : (8 * a + b) % 8 = b := by omega
  rw [h1, h2]

end Par

@[expose] noncomputable def qbF (c e p q GT BMS t : Nat) : Nat :=
  Nat.xor (xorN 8 fun a => nIf(bit (sqK c e (wK p q (pw2 a))) t, fget BMS a 256, 0))
    (xorN 64 fun ab => (fun a b => nIf(andB (Nat.blt a b)
      (bit (fget GT (Nat.add (Nat.mul 8 a) b) 3) t),
      Nat.land (fget BMS a 256) (fget BMS b 256), 0)) (Nat.div ab 8) (Nat.mod ab 8))

theorem qbF_lt (c e p q GT BMS t : Nat) : qbF c e p q GT BMS t < 2 ^ 256 := by
  unfold qbF
  rw [nat_xor_eq]
  refine Nat.xor_lt_two_pow (xorN_lt fun a _ => ?_) (xorN_lt fun ab _ => ?_)
  · rw [nIf_eq]; split
    · exact fget_lt _ _ _
    · exact Nat.two_pow_pos _
  · simp only [nIf_eq]; split
    · rw [nat_land_eq]; exact Nat.and_lt_two_pow _ (fget_lt _ _ _)
    · exact Nat.two_pow_pos _

theorem testBit_nIf (b : Bool) (x y j : Nat) :
    (Bool.rec (motive := fun _ => Nat) y x b).testBit j =
      if b then x.testBit j else y.testBit j := by
  cases b <;> rfl

namespace Par

variable {c e p q : Nat} (P : Par c e p q)
include P

theorem testBit_qbF {t w : Nat} (hw : w < 256) :
    (qbF c e p q (gtK c p q) BM t).testBit w = (Qi c e p q w).testBit t := by
  unfold qbF
  rw [nat_xor_eq, Nat.testBit_xor, testBit_xorN, testBit_xorN, P.Qi_expand hw, Nat.testBit_xor,
    testBit_xorN, testBit_xorN]
  refine congrArg₂ (fun a b => a ^^ b) ?_ ?_
  · apply bxorN_congr; intro a ha
    rw [testBit_nIf, bit_eq, pw2_eq, BM_field ha]
    change (if (Qi c e p q (2 ^ a)).testBit t = true then _ else _) = _
    cases h1 : (Qi c e p q (2 ^ a)).testBit t <;> cases h2 : w.testBit a <;>
      simp [testBit_bmK, hw, h1, h2]
  · apply bxorN_congr; intro ab hab
    have ha : ab / 8 < 8 := by omega
    have hb : ab % 8 < 8 := Nat.mod_lt _ (by omega)
    simp only [testBit_nIf, andB_eq, nat_blt_eq, bit_eq, nat_add_eq, nat_mul_eq, nat_div_eq,
      nat_mod_eq, gtK_field c p q ha hb, BM_field ha, BM_field hb, nat_land_eq]
    by_cases hab' : ab / 8 < ab % 8
    · cases h1 : (Bi c p q (2 ^ (ab / 8)) (2 ^ (ab % 8))).testBit t <;>
        cases h2 : w.testBit (ab / 8) <;> cases h3 : w.testBit (ab % 8) <;>
        simp [testBit_bmK, Nat.testBit_and, hw, h1, h2, h3, hab']
    · simp [hab']

theorem testBit_cmQ {v w : Nat} (hv : v < 8) (hw : w < 256) :
    (fget (cmQ c e p q (gtK c p q) BM) v 256).testBit w = decide (Qi c e p q w = v) := by
  have hQB : ∀ t < 3, fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) t 256 =
      qbF c e p q (gtK c p q) BM t := fun t ht => orN_field (fun i _ => qbF_lt _ _ _ _ _ _ i) ht
  have hS : ∀ v t, t < 3 → Bool.rec (motive := fun _ => Nat)
      (ALL ^^^ fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) t 256)
      (fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) t 256) (bit v t) <
        2 ^ 256 := by
    intro v t ht
    rw [nIf_eq, hQB t ht]; split
    · exact qbF_lt _ _ _ _ _ _ _
    · exact ALL_xor_lt (qbF_lt _ _ _ _ _ _ _)
  have hcm : cmQ c e p q (gtK c p q) BM = orN 8 (fun v =>
      (Bool.rec (motive := fun _ => Nat)
        (ALL ^^^ fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 0 256)
        (fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 0 256) (bit v 0) &&&
      (Bool.rec (motive := fun _ => Nat)
        (ALL ^^^ fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 1 256)
        (fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 1 256) (bit v 1) &&&
      Bool.rec (motive := fun _ => Nat)
        (ALL ^^^ fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 2 256)
        (fget (orN 3 fun t => qbF c e p q (gtK c p q) BM t <<< (256 * t)) 2 256) (bit v 2)))
      <<< (256 * v)) := by
    unfold cmQ; rw [strictN_eq]; rfl
  rw [hcm, orN_field (fun i _ => Nat.and_lt_two_pow _ (Nat.and_lt_two_pow _ (hS i 2 (by omega))))
    hv]
  simp only [Nat.testBit_and, testBit_nIf, bit_eq, hQB 0 (by omega), hQB 1 (by omega),
    hQB 2 (by omega), testBit_ALL_xor hw, P.testBit_qbF hw]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · intro h
    apply eq_of_low3 (Qi_lt _ _ _ _ _) hv
    intro t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl <;>
      cases h1 : (Qi c e p q w).testBit _ <;> cases h2 : v.testBit _ <;> simp_all
  · intro h
    subst h
    cases (Qi c e p q w).testBit 0 <;> cases (Qi c e p q w).testBit 1 <;>
      cases (Qi c e p q w).testBit 2 <;> simp

theorem testBit_perpK {y x : Nat} (hy : y < 256) (hx : x < 256) :
    (perpK (maK c p q) y).testBit x = decide (Bi c p q y x = 0) := by
  unfold perpK
  rw [strictN_eq, nat_xor_eq, testBit_ALL_xor hx]
  simp only [nat_lor_eq, Nat.testBit_or, P.testBit_xwK hy hx (by omega : 0 < 3),
    P.testBit_xwK hy hx (by omega : 1 < 3), P.testBit_xwK hy hx (by omega : 2 < 3)]
  have hB := Bi_lt c p q y x
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    apply eq_of_low3 hB (by omega)
    intro t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · intro h; rw [h]; simp

end Par

theorem perpK_lt (MA y : Nat) : perpK MA y < 2 ^ 256 := by
  unfold perpK
  rw [strictN_eq]
  exact ALL_xor_lt (by
    simp only [nat_lor_eq]
    exact Nat.or_lt_two_pow (fget_lt _ _ _) (Nat.or_lt_two_pow (fget_lt _ _ _) (fget_lt _ _ _)))

theorem testBit_eqCnt {CN v x : Nat} (hx : x < 256) :
    (eqCnt CN v).testBit x = true ↔ ∀ i < 9, (fget CN i 256).testBit x = v.testBit i := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) ALL (fun i ih => Nat.land ih
      (Bool.rec (motive := fun _ => Nat) (Nat.xor ALL (fget CN i (nat_lit 256)))
        (fget CN i (nat_lit 256)) (bit v i))) n).testBit x = true ↔
      ∀ i < n, (fget CN i 256).testBit x = v.testBit i := by
    intro n
    induction n with
    | zero =>
      change ALL.testBit x = true ↔ _
      rw [ALL_eq, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => hx⟩
    | succ n ih =>
      change (Nat.land _ _).testBit x = true ↔ _
      rw [nat_land_eq, Nat.testBit_and, Bool.and_eq_true, ih, testBit_nIf, bit_eq]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h1 i hi
        · cases hv : v.testBit i <;> simp_all [testBit_ALL_xor hx]
      · intro h
        refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
        have := h n (Nat.lt_succ_self n)
        cases hv : v.testBit n <;> simp_all [testBit_ALL_xor hx]
  exact key 9

theorem testBit_cntAt (CN x i : Nat) :
    (cntAt CN x).testBit i = (decide (i < 9) && (fget CN i 256).testBit x) := by
  unfold cntAt
  rw [Bool.eq_iff_iff, orN_testBit]
  simp only [nat_shiftLeft_eq, bitN_eq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i', hi', h⟩
    split at h
    · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at h
      have : i' = i := by simpa using h
      subst this; exact ⟨hi', by assumption⟩
    · simp at h
  · rintro ⟨hi, h⟩
    exact ⟨i, hi, by simp [h, Nat.shiftLeft_eq]⟩

theorem testBit_lvK {c e p q CM CN k w : Nat} (hk : k < 8) (hw : w < 256) :
    (fget (lvK c e p q CM CN) k 256).testBit w = true ↔
      (fget CM (Qi c e p q (bidx k)) 256).testBit w = true ∧
        ∀ i < 9, (fget CN i 256).testBit w = (fget CN i 256).testBit (bidx k) := by
  have : lvK c e p q CM CN = orN 8 (fun k => (fget CM (sqK c e (wK p q (bidx k))) 256 &&&
      eqCnt CN (cntAt CN (bidx k))) <<< (256 * k)) := rfl
  rw [this, orN_field (fun i _ => by rw [Nat.and_comm]; exact Nat.and_lt_two_pow _ (fget_lt _ _ _))
    hk]
  rw [Nat.testBit_and, Bool.and_eq_true, testBit_eqCnt hw]
  simp only [testBit_cntAt]
  refine and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun hi => ?_)
  simp [hi]

@[expose] noncomputable def step256 (i s : Nat) : Nat :=
  Nat.lor
    (Nat.xor (Nat.land s (maskN 2304)) (Nat.shiftLeft (Nat.shiftRight s 2304) (Nat.mul 256 i)))
    (Nat.shiftLeft (Nat.land (fget s i 256) (Nat.shiftRight s 2304)) 2304)

@[expose] noncomputable def step1 (i t : Nat) : Nat :=
  ((t &&& 511) ^^^ ((t >>> 9) <<< i)) ||| ((fget t i 1 &&& (t >>> 9)) <<< 9)

theorem foldUp_succ (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp (n + 1) f s = f n (foldUp n f s) := by
  change strictN (foldUp n f s) (f n) = _
  rw [strictN_eq]

theorem addCnt_eq (S m : Nat) :
    addCnt S m = foldUp 9 step256 (S ||| m <<< 2304) &&& maskN 2304 := rfl

@[expose] noncomputable def colV (s x : Nat) : Nat :=
  orN 10 fun i => if s.testBit (256 * i + x) then 2 ^ i else 0

theorem testBit_colV (s x i : Nat) :
    (colV s x).testBit i = (decide (i < 10) && s.testBit (256 * i + x)) := by
  unfold colV
  rw [Bool.eq_iff_iff, orN_testBit]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i', hi', h⟩
    split at h
    · rw [Nat.testBit_two_pow] at h
      have : i' = i := by simpa using h
      subst this; exact ⟨hi', by assumption⟩
    · simp at h
  · rintro ⟨hi, h⟩
    exact ⟨i, hi, by simp [h]⟩

theorem colV_lt (s x : Nat) : colV s x < 1024 := by
  unfold colV
  apply orN_lt (w := 10)
  intro i hi; split
  · exact Nat.pow_lt_pow_right (by omega) hi
  · exact Nat.two_pow_pos _

set_option exponentiation.threshold 4096 in
theorem testBit_step256 {s i i' x : Nat} (hs : s < 2 ^ 2560) (hi : i < 9) (hi' : i' < 10)
    (hx : x < 256) : (step256 i s).testBit (256 * i' + x) =
      if i' < 9 then (s.testBit (256 * i' + x) ^^ (decide (i' = i) && s.testBit (2304 + x)))
      else (s.testBit (256 * i + x) && s.testBit (2304 + x)) := by
  have hz : ∀ j, 2560 ≤ j → s.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) hj))
  simp only [step256, nat_lor_eq, nat_xor_eq, nat_land_eq, nat_shiftLeft_eq, nat_shiftRight_eq,
    nat_mul_eq, maskN_eq, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_fget]
  by_cases h9 : i' < 9
  · have e1 : 256 * i' + x < 2304 := by omega
    have e2 : ¬ (256 * i' + x ≥ 2304) := by omega
    simp only [h9, e1, e2, ↓reduceIte, decide_true, decide_false, Bool.false_and,
      Bool.or_false]
    rcases Nat.lt_trichotomy i' i with h1 | h1 | h1
    · have h2 : ¬ (256 * i' + x ≥ 256 * i) := by omega
      have h3 : i' ≠ i := by omega
      simp [h2, h3]
    · subst h1
      simp
    · rw [hz (2304 + (256 * i' + x - 256 * i)) (by omega)]
      have h3 : i' ≠ i := by omega
      simp [h3]
  · have hi9 : i' = 9 := by omega
    subst hi9
    have e3 : 2304 + (256 * 9 + x - 256 * i) ≥ 2560 := by omega
    have e5 : ¬ (9 < 9) := by omega
    have e6 : ¬ (256 * 9 + x < 2304) := by omega
    simp only [e5, ↓reduceIte, e6, decide_false, Bool.false_xor, hz _ e3, Bool.and_false,
      Bool.false_or]
    have e4 : 256 * 9 + x - 2304 = x := by omega
    simp [e4, hx, Nat.mul_comm i 256]

theorem testBit_step1 {t i i' : Nat} (ht : t < 1024) (hi : i < 9) (hi' : i' < 10) :
    (step1 i t).testBit i' =
      if i' < 9 then (t.testBit i' ^^ (decide (i' = i) && t.testBit 9))
      else (t.testBit i && t.testBit 9) := by
  have hz : ∀ j, 10 ≤ j → t.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by omega) hj :
      2 ^ 10 ≤ 2 ^ j))
  have h511 : (511 : Nat) = 2 ^ 9 - 1 := rfl
  simp only [step1, h511, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_fget]
  by_cases h9 : i' < 9
  · have e1 : ¬ (i' ≥ 9) := by omega
    simp only [h9, ↓reduceIte, decide_true, e1, decide_false, Bool.false_and, Bool.or_false]
    rcases Nat.lt_trichotomy i' i with h1 | h1 | h1
    · have h2 : ¬ (i' ≥ i) := by omega
      have h3 : i' ≠ i := by omega
      simp [h2, h3]
    · subst h1; simp
    · rw [hz (9 + (i' - i)) (by omega)]
      have h2 : i' ≥ i := by omega
      have h3 : i' ≠ i := by omega
      simp [h2, h3]
  · have hi9 : i' = 9 := by omega
    subst hi9
    rw [hz (9 + (9 - i)) (by omega)]
    simp [Nat.mul_comm i 1]

set_option exponentiation.threshold 4096 in
theorem step256_lt {s i : Nat} (hs : s < 2 ^ 2560) (hi : i < 9) : step256 i s < 2 ^ 2560 := by
  simp only [step256, nat_lor_eq, nat_xor_eq, nat_land_eq, nat_shiftLeft_eq, nat_shiftRight_eq,
    nat_mul_eq, maskN_eq]
  have hc : s >>> 2304 < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hs)
  refine Nat.or_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · exact Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega)))
      (Nat.le_of_lt (Nat.pow_lt_pow_right (by omega) (by omega)))
  · rw [Nat.shiftLeft_eq]
    calc (s >>> 2304) * 2 ^ (256 * i) < 2 ^ 256 * 2 ^ (256 * i) :=
          Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)
      _ = 2 ^ (256 + 256 * i) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ 2560 := Nat.pow_le_pow_right (by omega) (by omega)
  · rw [Nat.shiftLeft_eq]
    calc (fget s i 256 &&& s >>> 2304) * 2 ^ 2304 < 2 ^ 256 * 2 ^ 2304 :=
          Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow _ hc) (Nat.two_pow_pos _)
      _ = 2 ^ 2560 := by rw [← Nat.pow_add]

theorem step1_lt {t i : Nat} (ht : t < 1024) (hi : i < 9) : step1 i t < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro j hj
  simp only [step1, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  have h1 : (511 : Nat).testBit j = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (by decide : 511 < 2 ^ 9) (Nat.pow_le_pow_right (by omega) (by omega)))
  have h2 : t.testBit (i + (j - i) + 0 + 9) = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by omega) (by omega) : 2 ^ 10 ≤ _))
  have h3 : t.testBit (9 + (j - i)) = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by omega) (by omega) : 2 ^ 10 ≤ _))
  have h4 : t.testBit (9 + (j - 9)) = false := Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by omega) (by omega) : 2 ^ 10 ≤ _))
  simp [h1, h3, h4]

theorem colV_step {s i x : Nat} (hs : s < 2 ^ 2560) (hi : i < 9) (hx : x < 256) :
    colV (step256 i s) x = step1 i (colV s x) := by
  apply Nat.eq_of_testBit_eq; intro i'
  rw [testBit_colV]
  rcases Nat.lt_or_ge i' 10 with hi' | hi'
  · rw [testBit_step256 hs hi hi' hx, testBit_step1 (colV_lt s x) hi hi']
    have e1 : (9 : Nat) < 10 := by omega
    have e2 : i < 10 := by omega
    simp only [testBit_colV, hi', decide_true, Bool.true_and, e1, e2]
  · have e1 : ¬ (i' < 10) := by omega
    simp only [e1, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (step1_lt (colV_lt s x) hi)
      (Nat.pow_le_pow_right (n := 2) (by omega) hi' : 2 ^ 10 ≤ 2 ^ i'))).symm

theorem foldUp_step1 : ∀ t < 1024, foldUp 9 step1 t &&& 511 = ((t &&& 511) + (t >>> 9)) % 512 := by
  decide +kernel

theorem colV_foldUp {s x : Nat} (hs : s < 2 ^ 2560) (hx : x < 256) :
    ∀ n ≤ 9, foldUp n step256 s < 2 ^ 2560 ∧ colV (foldUp n step256 s) x = foldUp n step1 (colV s x)
  | 0, _ => ⟨hs, rfl⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := colV_foldUp hs hx n (by omega)
    rw [foldUp_succ, foldUp_succ, colV_step h1 (by omega) hx, h2]
    exact ⟨step256_lt h1 (by omega), rfl⟩

set_option exponentiation.threshold 4096 in
theorem colV_addCnt {S m x : Nat} (hS : S < 2 ^ 2304) (hm : m < 2 ^ 256) (hx : x < 256) :
    addCnt S m < 2 ^ 2304 ∧
      colV (addCnt S m) x = (colV S x + if m.testBit x then 1 else 0) % 512 := by
  have hs0 : S ||| m <<< 2304 < 2 ^ 2560 := by
    refine Nat.or_lt_two_pow (Nat.lt_trans hS (Nat.pow_lt_pow_right (by omega) (by omega))) ?_
    rw [Nat.shiftLeft_eq]
    calc m * 2 ^ 2304 < 2 ^ 256 * 2 ^ 2304 := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
      _ = 2 ^ 2560 := by rw [← Nat.pow_add]
  obtain ⟨-, hf⟩ := colV_foldUp hs0 hx 9 (Nat.le_refl 9)
  rw [addCnt_eq, maskN_eq]
  refine ⟨Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega)), ?_⟩
  have hmask : ∀ X, colV (X &&& 2 ^ 2304 - 1) x = colV X x &&& 511 := by
    intro X
    apply Nat.eq_of_testBit_eq; intro i
    have e511 : (511 : Nat) = 2 ^ 9 - 1 := rfl
    rw [testBit_colV, Nat.testBit_and, Nat.testBit_and, testBit_colV,
      Nat.testBit_two_pow_sub_one, e511, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 9
    · have e1 : i < 10 := by omega
      have e2 : 256 * i + x < 2304 := by omega
      simp [hi, e1, e2]
    · have e2 : ¬ (256 * i + x < 2304) := by omega
      simp [hi, e2]
  rw [hmask, hf, foldUp_step1 _ (colV_lt _ _)]
  have hS9 : ∀ i, 9 ≤ i → S.testBit (256 * i + x) = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega) (by omega)))
  have h1 : colV (S ||| m <<< 2304) x &&& 511 = colV S x := by
    apply Nat.eq_of_testBit_eq; intro i
    have e511 : (511 : Nat) = 2 ^ 9 - 1 := rfl
    rw [Nat.testBit_and, testBit_colV, testBit_colV, e511,
      Nat.testBit_two_pow_sub_one, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : i < 9
    · have e1 : i < 10 := by omega
      have e2 : ¬ (256 * i + x ≥ 2304) := by omega
      simp [hi, e1, e2]
    · simp only [hi, decide_false, Bool.and_false]
      by_cases hi10 : i < 10
      · simp [hi10, hS9 i (by omega)]
      · simp [hi10]
  have h2 : colV (S ||| m <<< 2304) x >>> 9 = if m.testBit x then 1 else 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_shiftRight, testBit_colV, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      have e1 : (9 : Nat) < 10 := by omega
      have e2 : 256 * 9 + x ≥ 2304 := by omega
      have e3 : 256 * 9 + x - 2304 = x := by omega
      simp only [Nat.add_zero, e1, decide_true, Bool.true_and, hS9 9 (Nat.le_refl 9),
        Bool.false_or, e2, e3]
      split <;> simp_all
    | succ i =>
      have e1 : ¬ (9 + (i + 1) < 10) := by omega
      simp only [e1, decide_false, Bool.false_and]
      split <;> simp [Nat.testBit_succ]
  rw [h1, h2]

theorem sumN_succ (n : Nat) (g : Nat → Nat) : sumN (n + 1) g = g n + sumN n g := rfl

theorem sumN_congr {n : Nat} {g g' : Nat → Nat} (h : ∀ i < n, g i = g' i) :
    sumN n g = sumN n g' := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN_succ, sumN_succ, h n (by omega), ih fun i hi => h i (by omega)]

theorem sumN_zero_fun (n : Nat) : sumN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN_succ, ih]

theorem sumN_split {n k : Nat} {g g' : Nat → Nat} (hk : k < n) (h : ∀ i, i ≠ k → g i = g' i)
    (h0 : g' k = 0) : sumN n g = sumN n g' + g k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumN_succ, sumN_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [h0, sumN_congr (fun i hi => h i (by omega))]; omega
    · rw [ih (by omega), h n (Ne.symm hkn)]; omega

theorem sumN_bottom (n : Nat) (g : Nat → Nat) :
    sumN (n + 1) g = g 0 + sumN n (fun j => g (j + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN_succ, ih, sumN_succ]; omega

theorem sumN_add (a b : Nat) (g : Nat → Nat) :
    sumN (a + b) g = sumN b (fun i => g (a + i)) + sumN a g := by
  induction b with
  | zero => simp; rfl
  | succ b ih => rw [← Nat.add_assoc, sumN_succ, ih, sumN_succ]; omega

theorem sumN_mul (m n : Nat) (g : Nat → Nat) :
    sumN (m * n) g = sumN m (fun a => sumN n (fun b => g (n * a + b))) := by
  induction m with
  | zero => rw [Nat.zero_mul]; rfl
  | succ m ih => rw [Nat.succ_mul, sumN_add, ih, sumN_succ, Nat.mul_comm m n]

theorem sumN_cut {n k : Nat} {g : Nat → Nat} (hk : k ≤ n) (h : ∀ i, k ≤ i → i < n → g i = 0) :
    sumN n g = sumN k g := by
  induction n with
  | zero => rw [Nat.le_zero.mp hk]
  | succ n ih =>
    rcases Nat.lt_or_ge n k with h1 | h1
    · have e : k = n + 1 := by omega
      rw [e]
    · rw [sumN_succ, h n h1 (Nat.lt_succ_self n), Nat.zero_add]
      exact ih h1 fun i hi1 hi2 => h i hi1 (Nat.lt_succ_of_lt hi2)

@[expose] noncomputable def wFoldF (f : Nat → Nat → Nat) (base n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih w s => nIf(Nat.beq w (nat_lit 0), s,
      (fun low => strictN (f (Nat.add base (CFSG.KC.Local.pop64 (Nat.sub low (nat_lit 1)))) s)
        (fun s2 => ih (Nat.xor w low) s2))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1)))))) n

theorem wordFold_eq (f : Nat → Nat → Nat) (base : Nat) :
    CFSG.KC.Local.wordFold f base = wFoldF f base 64 := rfl

@[expose] noncomputable def outerF (f : Nat → Nat → Nat) (M' J : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih j s => strictN (CFSG.KC.Local.wordFold f (Nat.shiftLeft j (nat_lit 6))
      (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6))) (nat_lit 18446744073709551615)) s)
      (fun s2 => ih (Nat.succ j) s2)) J

theorem foldBits_eq (n : Nat) (f : Nat → Nat → Nat) (M s : Nat) :
    CFSG.KC.Local.foldBits n f M s = outerF f (M &&& ((1 <<< n) - 1)) ((n + 63) >>> 6) 0 s := rfl

theorem outerF_succ (f : Nat → Nat → Nat) (M' J j₀ s : Nat) :
    outerF f M' (J + 1) j₀ s =
      outerF f M' J (j₀ + 1) (wFoldF f (64 * j₀) 64 ((M' >>> (64 * j₀)) % 2 ^ 64) s) := by
  change strictN (CFSG.KC.Local.wordFold f (Nat.shiftLeft j₀ 6)
    (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j₀ 6)) 18446744073709551615) s)
    (fun s2 => outerF f M' J (Nat.succ j₀) s2) = _
  rw [strictN_eq, wordFold_eq, nat_shiftLeft_eq, nat_shiftRight_eq, nat_land_eq, land_max,
    Nat.shiftLeft_eq, Nat.mul_comm j₀]

section Count

variable {f : Nat → Nat → Nat} {φ : Nat → Nat} {I : Nat → Prop} {δ : Nat → Nat}
  (hφ : ∀ s, I s → φ s < 512) (hf : ∀ y s, I s → I (f y s) ∧ φ (f y s) = (φ s + δ y) % 512)
include hφ hf

theorem wFoldF_count (base : Nat) : ∀ n w s, w < 2 ^ 64 → (∀ i < 64 - n, w.testBit i = false) →
    I s → I (wFoldF f base n w s) ∧ φ (wFoldF f base n w s) =
      (φ s + sumN 64 (fun k => if w.testBit k then δ (base + k) else 0)) % 512
  | n, w, s, hw, hlow, hs => by
    by_cases hw0 : w = 0
    · subst hw0
      have : wFoldF f base n 0 s = s := by cases n <;> rfl
      rw [this, sumN_congr (g' := fun _ => 0) (fun i _ => by simp), sumN_zero_fun, Nat.add_zero,
        Nat.mod_eq_of_lt (hφ s hs)]
      exact ⟨hs, rfl⟩
    cases n with
    | zero =>
      exfalso; apply hw0
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge i 64 with hi | hi
      · exact hlow i (by omega)
      · exact testBit_false_of_lt hw hi
    | succ n =>
      obtain ⟨k0, hl, hk0, hlt⟩ := lowBit_spec w hw0
      have hk064 : k0 < 64 := by
        by_contra hc; rw [testBit_false_of_lt hw (by omega)] at hk0; exact absurd hk0 (by decide)
      have hk0n : 64 - (n + 1) ≤ k0 := by
        by_contra hc; rw [hlow k0 (by omega)] at hk0; exact absurd hk0 (by decide)
      have hstep :
          wFoldF f base (n + 1) w s = wFoldF f base n (w ^^^ 2 ^ k0) (f (base + k0) s) := by
        have h1 : wFoldF f base (n + 1) w s = Bool.rec (motive := fun _ => Nat)
            ((fun low => strictN (f (Nat.add base (CFSG.KC.Local.pop64 (Nat.sub low 1))) s)
              (fun s2 => wFoldF f base n (Nat.xor w low) s2))
              (Nat.land w (Nat.xor w (Nat.sub w 1)))) s (Nat.beq w 0) := rfl
        have hb : Nat.beq w 0 = false := by rw [nat_beq_eq]; simpa using hw0
        rw [h1, hb]
        simp only [strictN_eq, nat_land_eq, nat_xor_eq, nat_sub_eq, nat_add_eq]
        rw [hl, pop64_pow k0 hk064]
      obtain ⟨hI1, hφ1⟩ := hf (base + k0) s hs
      obtain ⟨hI2, hφ2⟩ := wFoldF_count base n (w ^^^ 2 ^ k0) (f (base + k0) s)
        (Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by omega) hk064)) (by
          intro i hi
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          rcases Nat.lt_or_ge i k0 with h1 | h1
          · rw [hlt i h1]; simp; omega
          · have : i = k0 := by omega
            simp [this, hk0]) hI1
      rw [hstep]
      refine ⟨hI2, ?_⟩
      have hsplit : sumN 64 (fun k => if w.testBit k then δ (base + k) else 0) =
          sumN 64 (fun k => if (w ^^^ 2 ^ k0).testBit k then δ (base + k) else 0) +
            δ (base + k0) := by
        rw [sumN_split (k := k0) (g := fun k => if w.testBit k then δ (base + k) else 0)
          (g' := fun k => if (w ^^^ 2 ^ k0).testBit k then δ (base + k) else 0) hk064
          (fun i hi => by rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [Ne.symm hi])
          (by rw [Nat.testBit_xor, Nat.testBit_two_pow, hk0]; simp)]
        simp [hk0]
      rw [hφ2, hφ1, hsplit]
      omega

theorem foldBits_count {n M s : Nat} (hs : I s) :
    I (CFSG.KC.Local.foldBits n f M s) ∧ φ (CFSG.KC.Local.foldBits n f M s) =
      (φ s + sumN n (fun y => if M.testBit y then δ y else 0)) % 512 := by
  have outer : ∀ (M' J j₀ s : Nat), I s → I (outerF f M' J j₀ s) ∧ φ (outerF f M' J j₀ s) =
        (φ s + sumN J (fun j => sumN 64 (fun k =>
          if M'.testBit (64 * (j₀ + j) + k) then δ (64 * (j₀ + j) + k) else 0))) % 512 := by
    intro M' J
    induction J with
    | zero =>
      intro j₀ s hs
      refine ⟨hs, ?_⟩
      change φ s = (φ s + 0) % 512
      rw [Nat.add_zero, Nat.mod_eq_of_lt (hφ s hs)]
    | succ J ih =>
      intro j₀ s hs
      rw [outerF_succ]
      obtain ⟨hI1, hφ1⟩ := wFoldF_count hφ hf (64 * j₀) 64 ((M' >>> (64 * j₀)) % 2 ^ 64) s
        (Nat.mod_lt _ (Nat.two_pow_pos 64)) (by simp) hs
      obtain ⟨hI2, hφ2⟩ := ih (j₀ + 1) _ hI1
      refine ⟨hI2, ?_⟩
      rw [hφ2, hφ1, sumN_bottom J]
      have hw : ∀ k < 64, (if ((M' >>> (64 * j₀)) % 2 ^ 64).testBit k then
          δ (64 * j₀ + k) else 0) =
          if M'.testBit (64 * (j₀ + 0) + k) then δ (64 * (j₀ + 0) + k) else 0 := by
        intro k hk
        rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
        simp only [hk, decide_true, Bool.true_and, Nat.add_zero, Nat.add_comm (64 * j₀) k]
      rw [sumN_congr hw]
      have e : ∀ j, j₀ + 1 + j = j₀ + (j + 1) := fun j => by omega
      simp only [e]
      omega
  rw [foldBits_eq]
  obtain ⟨h1, h2⟩ := outer _ _ 0 s hs
  refine ⟨h1, ?_⟩
  have hsum : (sumN ((n + 63) >>> 6) fun j => sumN 64 fun k =>
      if (M &&& ((1 <<< n) - 1)).testBit (64 * (0 + j) + k) then δ (64 * (0 + j) + k) else 0) =
      sumN n (fun y => if M.testBit y then δ y else 0) := by
    simp only [Nat.zero_add]
    rw [← sumN_mul (g := fun y => if (M &&& ((1 <<< n) - 1)).testBit y then δ y else 0)]
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
    rw [sumN_cut (k := n) (by omega) (fun i hi _ => by
      rw [Nat.testBit_mod_two_pow]; simp; omega)]
    apply sumN_congr
    intro i hi
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [h2, hsum]

end Count

set_option exponentiation.threshold 4096 in
theorem colV_n0K {MA Z x : Nat} (hx : x < 256) :
    colV (n0K MA Z) x = sumN 256 (fun y => if Z.testBit y then
      (if (perpK MA y).testBit x then 1 else 0) else 0) % 512 := by
  have hφ : ∀ S, S < 2 ^ 2304 → colV S x < 512 := by
    intro S hS
    apply Nat.lt_pow_two_of_testBit (n := 9)
    intro i hi
    rw [testBit_colV]
    by_cases h10 : i < 10
    · simp only [h10, decide_true, Bool.true_and]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega)
        (by omega)))
    · simp [h10]
  have hf : ∀ y S, S < 2 ^ 2304 → addCnt S (perpK MA y) < 2 ^ 2304 ∧
      colV (addCnt S (perpK MA y)) x =
        (colV S x + if (perpK MA y).testBit x then 1 else 0) % 512 :=
    fun y S hS => colV_addCnt hS (perpK_lt MA y) hx
  have h := (foldBits_count (f := fun y S => addCnt S (perpK MA y)) (φ := fun S => colV S x)
    (I := fun S => S < 2 ^ 2304) (δ := fun y => if (perpK MA y).testBit x then 1 else 0)
    hφ hf (n := 256) (M := Z) (s := 0) (Nat.two_pow_pos _)).2
  have h0 : colV 0 x = 0 := by
    apply Nat.eq_of_testBit_eq; intro i; simp [testBit_colV]
  change colV (CFSG.KC.Local.foldBits 256 (fun y S => addCnt S (perpK MA y)) Z 0) x = _
  rw [h, h0, Nat.zero_add]

@[expose] def encF (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (encF w f k <<< w) ||| f k

theorem encF_lt {w : Nat} {f : Nat → Nat} (hf : ∀ j, f j < 2 ^ w) : ∀ k, encF w f k < 2 ^ (w * k)
  | 0 => by simp [encF]
  | k + 1 => by
    rw [encF, ← Nat.shiftLeft_add_eq_or_of_lt (hf k), Nat.shiftLeft_eq]
    have := encF_lt hf k
    calc encF w f k * 2 ^ w + f k < encF w f k * 2 ^ w + 2 ^ w := by have := hf k; omega
      _ = (encF w f k + 1) * 2 ^ w := by rw [Nat.succ_mul]
      _ ≤ 2 ^ (w * k) * 2 ^ w := Nat.mul_le_mul_right _ this
      _ = 2 ^ (w * (k + 1)) := by rw [← Nat.pow_add, Nat.mul_succ]

theorem fget_encF {w : Nat} {f : Nat → Nat} (hf : ∀ j, f j < 2 ^ w) :
    ∀ k i, i < k → fget (encF w f k) i w = f (k - 1 - i)
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, i, hi => by
    rw [encF, ← Nat.shiftLeft_add_eq_or_of_lt (hf k), Nat.shiftLeft_eq, fget_eq]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.add_mod, Nat.mul_mod_left,
        Nat.zero_add, Nat.mod_eq_of_lt (hf k)]
      simp
    | succ i =>
      have hd : (encF w f k * 2 ^ w + f k) / 2 ^ w = encF w f k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (hf k),
          Nat.zero_add]
      rw [Nat.succ_mul, Nat.add_comm (i * w) w, Nat.pow_add, ← Nat.div_div_eq_div_mul, hd,
        ← fget_eq, fget_encF hf k i (by omega)]
      congr 1; omega

@[expose] noncomputable def candR (TT XS k C n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) C (fun j ih =>
    (fun v X => Nat.land ih (Nat.land
      (nIf(bit v (nat_lit 0), fget X (nat_lit 0) (nat_lit 256),
        Nat.xor ALL (fget X (nat_lit 0) (nat_lit 256))))
      (Nat.land
        (nIf(bit v (nat_lit 1), fget X (nat_lit 1) (nat_lit 256),
          Nat.xor ALL (fget X (nat_lit 1) (nat_lit 256))))
        (nIf(bit v (nat_lit 2), fget X (nat_lit 2) (nat_lit 256),
          Nat.xor ALL (fget X (nat_lit 2) (nat_lit 256)))))))
    (fget TT (Nat.add (Nat.mul (nat_lit 8) j) k) (nat_lit 3))
    (fget XS (Nat.sub (Nat.sub k j) (nat_lit 1)) (nat_lit 768))) n

theorem testBit_nIf_ALL {b : Bool} {X w : Nat} (hw : w < 256) :
    (Bool.rec (motive := fun _ => Nat) (Nat.xor ALL X) X b).testBit w = (b == X.testBit w) := by
  cases b <;> simp [testBit_ALL_xor hw]

theorem candK_mem {TT XS k C w : Nat} (hw : w < 256) (hC : C.testBit w = true)
    (h : ∀ j < k, ∀ t < 3, (fget TT (8 * j + k) 3).testBit t =
      (fget (fget XS (k - 1 - j) 768) t 256).testBit w) : (candK TT XS k C).testBit w = true := by
  have key : ∀ n ≤ k, (candR TT XS k C n).testBit w = true := by
    intro n hn
    induction n with
    | zero => exact hC
    | succ n ih =>
      change (Nat.land (candR TT XS k C n) _).testBit w = true
      have hn' := h n (by omega)
      have e : k - n - 1 = k - 1 - n := by omega
      simp only [nat_land_eq, Nat.testBit_and, testBit_nIf_ALL hw, bit_eq, Bool.and_eq_true,
        ih (by omega), nat_add_eq, nat_mul_eq, nat_sub_eq, e, hn' 0 (by omega),
        hn' 1 (by omega), hn' 2 (by omega), beq_self_eq_true, and_self]
  exact key k (Nat.le_refl k)

theorem fget_BIDR : ∀ i < 8, fget BIDR (7 - i) 8 = bidx i := by decide +kernel

theorem bidx_eq : ∀ i < 8, bidx i = 2 ^ abit i ∧ abit i < 8 := by decide +kernel

theorem c3Ext_sound {MA TT LV : Nat} {a : Nat → Nat} (ha : ∀ j, a j < 256)
    (hval : ∀ i < 8, (fget LV i 256).testBit (a i) = true ∧ ∀ j < i, ∀ t < 3,
      (fget TT (8 * j + i) 3).testBit t = (fget (xwK MA (a j)) t 256).testBit (a i)) :
    ∀ d k, k + d = 8 → c3Ext MA TT LV d k (encF 8 a k) (encF 768 (fun j => xwK MA (a j)) k) =
      true → encF 8 a 8 = BIDR
  | 0, k, hk, h => by
    rw [Nat.add_zero] at hk
    subst hk
    change Nat.beq _ BIDR = true at h
    rw [nat_beq_eq, beq_iff_eq] at h
    exact h
  | d + 1, k, hk, h => by
    change strictB (candK TT (encF 768 (fun j => xwK MA (a j)) k) k (fget LV k 256)) (fun C =>
      CFSG.KC.Local.allBits 256 (fun w => c3Ext MA TT LV d (Nat.succ k)
        (Nat.lor (Nat.shiftLeft (encF 8 a k) 8) w)
        (Nat.lor (Nat.shiftLeft (encF 768 (fun j => xwK MA (a j)) k) 768) (xwK MA w))) C) =
      true at h
    rw [strictB_eq] at h
    have hk8 : k < 8 := by omega
    have hmem : (candK TT (encF 768 (fun j => xwK MA (a j)) k) k (fget LV k 256)).testBit (a k) =
        true := by
      refine candK_mem (ha k) (hval k hk8).1 fun j hj t ht => ?_
      have e : k - 1 - (k - 1 - j) = j := by omega
      rw [fget_encF (fun j => xwK_lt MA (a j)) k (k - 1 - j) (by omega), e]
      exact (hval k hk8).2 j hj t ht
    exact c3Ext_sound ha hval d (k + 1) (by omega) (allBits_spec h (a k) (ha k) hmem)

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have := xor_cancel_left a b
  rw [h, Nat.xor_zero] at this
  exact this

theorem xorN_single {n b : Nat} {f : Nat → Nat} (h : ∀ i, i ≠ b → f i = 0) :
    xorN n f = if b < n then f b else 0 := by
  induction n with
  | zero => simp [xorN_zero]
  | succ n ih =>
    rw [xorN_succ, ih]
    by_cases hb : b = n
    · subst hb; simp
    · rw [h n (Ne.symm hb), Nat.zero_xor]
      have : (b < n + 1) ↔ (b < n) := by omega
      simp only [this]

@[expose] def sig (b : Nat) : Nat := [2, 5, 1, 4, 7, 0, 3, 6].getD b 0

theorem sig_spec : ∀ b < 8, sig b < 8 ∧ abit (sig b) = b := by decide +kernel

theorem sig_abit : ∀ i < 8, sig (abit i) = i := by decide +kernel

@[expose] noncomputable def Lmap (a : Nat → Nat) (x : Nat) : Nat :=
  xorN 8 fun b => if x.testBit b then a (sig b) else 0

theorem Lmap_xor (a : Nat → Nat) (x y : Nat) : Lmap a (x ^^^ y) = Lmap a x ^^^ Lmap a y := by
  rw [Lmap, Lmap, Lmap, ← xorN_xor]
  apply xorN_congr; intro b _
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> simp

theorem Lmap_zero (a : Nat → Nat) : Lmap a 0 = 0 := by
  rw [Lmap, xorN_congr (g := fun _ => 0) (fun i _ => by simp), xorN_zero_fun]

theorem Lmap_lt {a : Nat → Nat} (ha : ∀ j, a j < 256) (x : Nat) : Lmap a x < 256 :=
  xorN_lt (w := 8) fun b _ => by split; exact ha _; exact Nat.two_pow_pos _

theorem Lmap_pow (a : Nat → Nat) {b : Nat} (hb : b < 8) : Lmap a (2 ^ b) = a (sig b) := by
  rw [Lmap, xorN_single (b := b) (fun i hi => by rw [Nat.testBit_two_pow]; simp [Ne.symm hi])]
  simp [hb]

theorem sumN_eq_sum (n : Nat) (g : Nat → Nat) : sumN n g = ((List.range n).map g).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumN_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp [Nat.add_comm]

theorem sumN_perm {n : Nat} {L : Nat → Nat} (hL : ∀ y < n, L y < n)
    (hinj : ∀ x y, x < n → y < n → L x = L y → x = y) (g : Nat → Nat) :
    sumN n (fun y => g (L y)) = sumN n g := by
  have hc : (fun y => g (L y)) = g ∘ L := rfl
  rw [sumN_eq_sum, sumN_eq_sum, hc, ← List.map_map]
  apply List.Perm.sum_eq
  apply List.Perm.map
  have hnd : ((List.range n).map L).Nodup :=
    List.Nodup.map_on (fun x hx y hy hxy => hinj x y (List.mem_range.mp hx) (List.mem_range.mp hy)
      hxy) List.nodup_range
  have hsub : (List.range n).map L ⊆ List.range n := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact List.mem_range.mpr (hL y (List.mem_range.mp hy))
  exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)

@[expose] noncomputable def N0 (c e p q x : Nat) : Nat :=
  sumN 256 fun y => if Qi c e p q y = 0 ∧ Bi c p q y x = 0 then 1 else 0

namespace Par

variable {c e p q : Nat} (P : Par c e p q)
include P

theorem radK_of {d : Nat} (hd : d < 256) (h : ∀ a < 8, Bi c p q (2 ^ a) d = 0) :
    (radK (maK c p q)).testBit d = true := by
  have key : ∀ n ≤ 24, (Nat.rec (motive := fun _ => Nat) ALL
      (fun i ih => Nat.land ih (Nat.xor ALL (fget (maK c p q) i (nat_lit 256)))) n).testBit d =
        true := by
    intro n hn
    induction n with
    | zero =>
      change ALL.testBit d = true
      rw [ALL_eq, Nat.testBit_two_pow_sub_one]; simpa using hd
    | succ n ih =>
      change (Nat.land _ (Nat.xor ALL _)).testBit d = true
      rw [nat_land_eq, nat_xor_eq, Nat.testBit_and, testBit_ALL_xor hd, ih (by omega)]
      have hn : n = 3 * (n / 3) + n % 3 := by omega
      rw [maK_field c p q (by omega), hn, P.testBit_maF (by omega) hd, h _ (by omega)]
      simp
  exact key 24 (by omega)

theorem N0_assign {a : Nat → Nat} (ha : ∀ j, a j < 256)
    (hQ : ∀ i < 8, Qi c e p q (a i) = Qi c e p q (bidx i))
    (hB : ∀ i < 8, ∀ j < i, Bi c p q (a j) (a i) = Bi c p q (bidx j) (bidx i))
    (hrad : (radK (maK c p q) &&& fget (cmQ c e p q (gtK c p q) BM) 0 256) = 1) :
    ∀ i < 8, N0 c e p q (a i) = N0 c e p q (bidx i) := by
  have hAB : ∀ b < 8, ∀ b' < 8, Bi c p q (a (sig b)) (a (sig b')) = Bi c p q (2 ^ b) (2 ^ b') := by
    intro b hb b' hb'
    obtain ⟨hs, hsa⟩ := sig_spec b hb
    obtain ⟨hs', hsa'⟩ := sig_spec b' hb'
    have e1 : bidx (sig b) = 2 ^ b := by rw [(bidx_eq _ hs).1, hsa]
    have e2 : bidx (sig b') = 2 ^ b' := by rw [(bidx_eq _ hs').1, hsa']
    rcases Nat.lt_trichotomy (sig b) (sig b') with h | h | h
    · rw [hB _ hs' _ h, e1, e2]
    · have hbb : b = b' := by rw [← hsa, ← hsa', h]
      subst hbb
      rw [P.Bi_self, P.Bi_self]
    · rw [P.Bi_symm, hB _ hs _ h, e1, e2, P.Bi_symm]
  have hQA : ∀ b < 8, Qi c e p q (a (sig b)) = Qi c e p q (2 ^ b) := by
    intro b hb
    obtain ⟨hs, hsa⟩ := sig_spec b hb
    rw [hQ _ hs, (bidx_eq _ hs).1, hsa]
  have hLlt := Lmap_lt ha
  have hBL : ∀ x < 256, ∀ y < 256, Bi c p q (Lmap a x) (Lmap a y) = Bi c p q x y := by
    intro x hx y hy
    have h1 : Bi c p q (Lmap a x) (Lmap a y) =
        xorN 8 (fun b => if x.testBit b then Bi c p q (a (sig b)) (Lmap a y) else 0) := by
      have := decomp (N := 8) (f := fun x => Bi c p q (Lmap a x) (Lmap a y))
        (by simp only [Lmap_zero, P.Bi_zero_left])
        (fun u v _ _ => by simp only [Lmap_xor]; exact P.Bi_xor_left (hLlt u) (hLlt v)) hx
      rw [this]
      apply xorN_congr; intro b hb
      rw [Lmap_pow a hb]
    rw [h1, P.Bi_decomp_left _ hx]
    apply xorN_congr; intro b hb
    congr 1
    have := decomp (N := 8) (f := fun y => Bi c p q (a (sig b)) (Lmap a y))
      (by simp only [Lmap_zero, P.Bi_zero_right])
      (fun u v _ _ => by simp only [Lmap_xor]; exact P.Bi_xor_right (hLlt u) (hLlt v)) hy
    rw [this, P.Bi_decomp_right _ hy]
    apply xorN_congr; intro b' hb'
    rw [Lmap_pow a hb', hAB b hb b' hb']
  have hQL : ∀ x < 256, Qi c e p q (Lmap a x) = Qi c e p q x := by
    intro x hx
    have hh := decomp (N := 8) (f := fun x => Qi c e p q (Lmap a x) ^^^ Qi c e p q x)
      (by simp only [Lmap_zero, P.Qi_zero, Nat.xor_self])
      (fun u v hu hv => by
        simp only [Lmap_xor]
        rw [P.Qi_xor (hLlt u) (hLlt v), P.Qi_xor hu hv, hBL u hu v hv]
        xsimp) hx
    rw [xorN_congr (g := fun _ => 0) (fun b hb => by
      rw [Lmap_pow a hb, hQA b hb, Nat.xor_self]; simp), xorN_zero_fun] at hh
    exact eq_of_xor_eq_zero hh
  have hinj : ∀ x y, x < 256 → y < 256 → Lmap a x = Lmap a y → x = y := by
    intro x y hx hy hxy
    have hd := xor_lt256 hx hy
    have hL0 : Lmap a (x ^^^ y) = 0 := by rw [Lmap_xor, hxy, Nat.xor_self]
    have hrad1 : (radK (maK c p q)).testBit (x ^^^ y) = true := by
      apply P.radK_of hd
      intro b hb
      have h2b : 2 ^ b < 256 := Nat.pow_lt_pow_right (by omega) (by omega : b < 8)
      rw [P.Bi_symm, ← hBL _ hd _ h2b, hL0, P.Bi_zero_left]
    have hcm : (fget (cmQ c e p q (gtK c p q) BM) 0 256).testBit (x ^^^ y) = true := by
      rw [P.testBit_cmQ (by omega) hd, ← hQL _ hd, hL0, P.Qi_zero]; rfl
    have h1 : (1 : Nat).testBit (x ^^^ y) = true := by
      rw [← hrad, Nat.testBit_and, hrad1, hcm]; rfl
    have : x ^^^ y = 0 := by
      by_contra hne
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
      exact hne h1
    exact eq_of_xor_eq_zero this
  intro i hi
  obtain ⟨hb, hab⟩ := bidx_eq i hi
  have hLi : Lmap a (bidx i) = a i := by rw [hb, Lmap_pow a hab, sig_abit i hi]
  have hbi : bidx i < 256 := by rw [hb]; exact Nat.pow_lt_pow_right (by omega) hab
  rw [← hLi, N0, N0]
  rw [← sumN_perm (L := Lmap a) (fun y _ => hLlt y) hinj]
  apply sumN_congr
  intro y hy
  rw [hQL y hy, hBL y hy _ hbi]

end Par

section Main

variable (mt : Array (Fin 8)) (tab : List (List V3)) (c e : Fin 8)

def ExtOK : List (V3 × V3) → List V3 → List V3 → Prop
  | _, [], [] => True
  | done, b :: bs, w :: ws => w ∈ tab.getD (Gen.sqN mt c e b).val [] ∧
      (∀ pr ∈ done, Gen.commN mt c pr.2 w = Gen.commN mt c pr.1 b) ∧ ExtOK ((b, w) :: done) bs ws
  | _, _, _ => False

theorem isoExt_of : ∀ (bs : List V3) (done : List (V3 × V3)),
    (∀ ws, ExtOK mt tab c e done bs ws → (∀ pr ∈ done, pr.1 = pr.2) ∧ ws = bs) →
      Gen.isoExt mt tab c e bs done = true
  | [], done, H => by
    obtain ⟨h1, -⟩ := H [] trivial
    rw [Gen.isoExt, List.all_eq_true]
    intro pr hpr
    rw [beq_iff_eq]; exact h1 pr hpr
  | b :: bs, done, H => by
    rw [Gen.isoExt, List.all_eq_true]
    intro w hw
    rw [Bool.or_eq_true]
    by_cases ht : (List.map (fun pr => (pr.2, Gen.commN mt c pr.1 b)) done).all
        (fun pr => Gen.commN mt c pr.1 w == pr.2) = true
    · right
      have hcond : ∀ pr ∈ done, Gen.commN mt c pr.2 w = Gen.commN mt c pr.1 b := by
        intro pr hpr
        rw [List.all_eq_true] at ht
        have := ht _ (List.mem_map_of_mem hpr)
        rwa [beq_iff_eq] at this
      apply isoExt_of bs ((b, w) :: done)
      intro ws' hws'
      obtain ⟨h1, h2⟩ := H (w :: ws') ⟨hw, hcond, hws'⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj h2
      refine ⟨fun pr hpr => ?_, rfl⟩
      rcases List.mem_cons.mp hpr with rfl | hpr
      · rfl
      · exact h1 pr hpr
    · left
      simpa using ht

theorem ExtOK_spec : ∀ (done : List (V3 × V3)) (bs ws : List V3), ExtOK mt tab c e done bs ws →
    ws.length = bs.length ∧ ∀ i (hi : i < bs.length) (hw : i < ws.length),
      ws[i] ∈ tab.getD (Gen.sqN mt c e bs[i]).val [] ∧
      ∀ j (hj : j < i), Gen.commN mt c ws[j] ws[i] = Gen.commN mt c bs[j] bs[i]
  | _, [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | done, b :: bs, w :: ws, ⟨h1, _, h3⟩ => by
    obtain ⟨hl, hk⟩ := ExtOK_spec ((b, w) :: done) bs ws h3
    refine ⟨by simp [hl], fun i hi hw => ?_⟩
    cases i with
    | zero => exact ⟨h1, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ i =>
      have hi' : i < bs.length := by simpa using hi
      have hw' : i < ws.length := by simpa using hw
      obtain ⟨k1, k2⟩ := hk i hi' hw'
      refine ⟨k1, fun j hj => ?_⟩
      cases j with
      | zero =>
        have := ExtOK_head ((b, w) :: done) bs ws h3 i hi' hw' (b, w) (List.mem_cons_self ..)
        exact this
      | succ j => exact k2 j (by omega)
  | _, [], _ :: _, h => absurd h (by simp [ExtOK])
  | _, _ :: _, [], h => absurd h (by simp [ExtOK])
where
  ExtOK_head : ∀ (done : List (V3 × V3)) (bs ws : List V3), ExtOK mt tab c e done bs ws →
      ∀ i (hi : i < bs.length) (hw : i < ws.length), ∀ pr ∈ done,
        Gen.commN mt c pr.2 ws[i] = Gen.commN mt c pr.1 bs[i]
    | _, [], [], _ => fun i hi => absurd hi (by simp)
    | done, b :: bs, w :: ws, ⟨_, h2, h3⟩ => by
      intro i hi hw pr hpr
      cases i with
      | zero => exact h2 pr hpr
      | succ i =>
        exact ExtOK_head ((b, w) :: done) bs ws h3 i (by simpa using hi) (by simpa using hw) pr
          (List.mem_cons_of_mem _ hpr)
    | _, [], _ :: _, h => absurd h (by simp [ExtOK])
    | _, _ :: _, [], h => absurd h (by simp [ExtOK])

end Main

theorem candTab_getD (mt : Array (Fin 8)) (c e : Fin 8) (W : List V3) (t : Fin 8) :
    (Gen.candTab mt c e W).getD t.val [] = W.filter fun w => Gen.sqN mt c e w == t := by
  rw [Gen.candTab, List.getD_eq_getElem _ _ (by simp [all8])]
  simp [all8]

@[expose] def idxW (p q : Fin 8) (x : V3) : Nat :=
  32 * x.1.val + 4 * x.2.1.val +
    (if x.2.2 = 0 then 0 else if x.2.2 = p then 1 else if x.2.2 = q then 2 else 3)

theorem idxW_lt (p q : Fin 8) (x : V3) : idxW p q x < 256 := by
  have := x.1.isLt; have := x.2.1.isLt
  unfold idxW; split
  · omega
  · split
    · omega
    · split <;> omega

theorem wPt_idxW {p q : Fin 8} {x : V3} (hx : x ∈ wList p q) : wPt p q (idxW p q x) = x := by
  obtain ⟨u, r, s⟩ := x
  have hs := mem_wList.mp hx
  simp only [lamList, List.mem_cons, List.not_mem_nil, or_false] at hs
  have key : ∃ t < 4, idxW p q (u, r, s) = 32 * u.val + 4 * r.val + t ∧ lamF p q t = s := by
    unfold idxW
    simp only
    by_cases h0 : s = 0
    · exact ⟨0, by omega, by simp [h0], by rw [lamF_0, h0]⟩
    by_cases h1 : s = p
    · have e1 : (s = p) = True := eq_true h1
      exact ⟨1, by omega, by simp only [h0, e1, ↓reduceIte], by rw [lamF_1, h1]⟩
    by_cases h2 : s = q
    · have e2 : (s = q) = True := eq_true h2
      exact ⟨2, by omega, by simp only [h0, h1, e2, ↓reduceIte], by rw [lamF_2, h2]⟩
    · refine ⟨3, by omega, by simp only [h0, h1, h2, ↓reduceIte], ?_⟩
      rw [lamF_3]
      rcases hs with h | h | h | h
      · exact absurd h h0
      · exact absurd h h1
      · exact absurd h h2
      · exact h.symm
  obtain ⟨t, ht, hi, hts⟩ := key
  rw [hi]
  have hu := u.isLt; have hr := r.isLt
  simp only [wPt]
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) ?_)
  · simp only; omega
  · simp only; omega
  · simp only
    rw [← hts]; congr 1; omega

theorem basisList_eq (p q : Fin 8) :
    basisList p q = (List.range 8).map fun i => wPt p q (bidx i) := by
  have hb : (List.range 8).map bidx = [32, 4, 1, 64, 8, 2, 128, 16] := by decide +kernel
  have e : ((List.range 8).map fun i => wPt p q (bidx i)) =
      ((List.range 8).map bidx).map (wPt p q) := by rw [List.map_map]; rfl
  rw [e, hb]
  simp only [basisList, List.map_cons, List.map_nil, wPt, Nat.reduceDiv, Nat.reduceMod, lamF_0,
    lamF_1, lamF_2]
  rfl

theorem c3Check_of {mt : Array (Fin 8)} (hM : bindMul mt = true) (hMul : mulOK = true)
    (hP : pairsOK = true) (h : ∀ c < 8, ∀ k < 7, c3Pair c k = true) : Gen.c3Check mt = true := by
  have L := mulLaws_of hMul
  unfold Gen.c3Check
  rw [List.all_eq_true]; intro c _
  rw [List.all_eq_true]; intro e _
  rw [List.all_eq_true]; intro p _
  rw [List.all_eq_true]; intro q _
  rw [Bool.or_eq_true]
  cases hcan : canon p q
  · left; rfl
  right
  rw [canon_eq] at hcan
  obtain ⟨k, hk, hkp, hkq⟩ := pairsOK_spec hP p.isLt q.isLt hcan
  have P : Par c.val e.val p.val q.val := ⟨c.isLt, e.isLt, p.isLt, q.isLt, L⟩
  have hC := h c.val c.isLt k (by lomega)
  unfold c3Pair at hC
  rw [hkp, hkq] at hC
  simp only [strictB_eq] at hC
  rw [allN_iff] at hC
  have hpar := hC e.val e.isLt
  unfold c3Par at hpar
  simp only [strictB_eq, andB_eq, Bool.and_eq_true, nat_beq_eq, beq_iff_eq, nat_land_eq] at hpar
  obtain ⟨hrad, hext⟩ := hpar
  apply isoExt_of
  intro ws hws
  refine ⟨fun pr hpr => absurd hpr (by simp), ?_⟩
  obtain ⟨hl, hspec⟩ := ExtOK_spec mt _ c e [] _ ws hws
  have hl8 : (basisList p q).length = 8 := by simp [basisList]
  let a : Nat → Nat := fun i => idxW p q (ws.getD i (0, 0, 0))
  have ha : ∀ j, a j < 256 := fun j => idxW_lt p q _
  have hbas : ∀ i (hi : i < (basisList p q).length), (basisList p q)[i] = wPt p q (bidx i) := by
    intro i hi
    simp only [basisList_eq, List.getElem_map, List.getElem_range]
  have hwi : ∀ i (hi : i < 8), ∃ (hw : i < ws.length), ws[i] ∈ wList p q ∧
      Gen.sqN mt c e ws[i] = Gen.sqN mt c e (wPt p q (bidx i)) ∧ wPt p q (a i) = ws[i] := by
    intro i hi
    have hw : i < ws.length := by omega
    have hmem := (hspec i (by omega) hw).1
    rw [candTab_getD, List.mem_filter, beq_iff_eq, hbas i (by omega)] at hmem
    refine ⟨hw, hmem.1, hmem.2, ?_⟩
    simp only [a, List.getD_eq_getElem _ _ hw]
    exact wPt_idxW hmem.1
  have hQ : ∀ i < 8, Qi c.val e.val p.val q.val (a i) = Qi c.val e.val p.val q.val (bidx i) := by
    intro i hi
    obtain ⟨hw, -, hsq, hpt⟩ := hwi i hi
    have hbi : bidx i < 256 := by
      rw [(bidx_eq i hi).1]; exact Nat.pow_lt_pow_right (by omega) (bidx_eq i hi).2
    rw [Qi, Qi, ← packV_wPt p q (ha i), ← packV_wPt p q hbi, ← sqN_packV hM, ← sqN_packV hM,
      hpt, hsq]
  have hB : ∀ i < 8, ∀ j < i, Bi c.val p.val q.val (a j) (a i) =
      Bi c.val p.val q.val (bidx j) (bidx i) := by
    intro i hi j hj
    obtain ⟨hw, -, -, hpt⟩ := hwi i hi
    obtain ⟨hw', -, -, hpt'⟩ := hwi j (by omega)
    have hbi : ∀ i < 8, bidx i < 256 := fun i hi => by
      rw [(bidx_eq i hi).1]; exact Nat.pow_lt_pow_right (by omega) (bidx_eq i hi).2
    have := (hspec i (by omega) hw).2 j hj
    rw [hbas i (by omega), hbas j (by omega)] at this
    rw [Bi, Bi, ← packV_wPt p q (ha i), ← packV_wPt p q (ha j), ← packV_wPt p q (hbi i hi),
      ← packV_wPt p q (hbi j (by omega)), ← commN_packV hM, ← commN_packV hM, hpt, hpt', this]
  have hN := P.N0_assign ha hQ hB hrad
  have hval : ∀ i < 8, (fget (lvK c.val e.val p.val q.val (cmQ c.val e.val p.val q.val
      (gtK c.val p.val q.val) BM) (n0K (maK c.val p.val q.val)
        (fget (cmQ c.val e.val p.val q.val (gtK c.val p.val q.val) BM) 0 256))) i 256).testBit
        (a i) = true ∧ ∀ j < i, ∀ t < 3,
      (fget (ttK c.val p.val q.val) (8 * j + i) 3).testBit t =
        (fget (xwK (maK c.val p.val q.val) (a j)) t 256).testBit (a i) := by
    intro i hi
    have hbi : bidx i < 256 := by
      rw [(bidx_eq i hi).1]; exact Nat.pow_lt_pow_right (by omega) (bidx_eq i hi).2
    refine ⟨?_, fun j hj t ht => ?_⟩
    · rw [testBit_lvK hi (ha i), P.testBit_cmQ (Qi_lt _ _ _ _ _) (ha i), decide_eq_true_iff]
      refine ⟨hQ i hi, fun i' hi' => ?_⟩
      have hcol : ∀ w < 256, (fget (n0K (maK c.val p.val q.val)
          (fget (cmQ c.val e.val p.val q.val (gtK c.val p.val q.val) BM) 0 256)) i' 256).testBit w =
          (N0 c.val e.val p.val q.val w % 512).testBit i' := by
        intro w hw
        have e1 : ∀ X, (fget X i' 256).testBit w = (colV X w).testBit i' := by
          intro X
          rw [testBit_fget, testBit_colV]
          have e : i' < 10 := by omega
          simp [hw, e, Nat.mul_comm i' 256]
        have hsum : (sumN 256 fun y =>
            if (fget (cmQ c.val e.val p.val q.val (gtK c.val p.val q.val) BM) 0 256).testBit y then
              (if (perpK (maK c.val p.val q.val) y).testBit w then 1 else 0) else 0) =
            N0 c.val e.val p.val q.val w := by
          unfold N0
          apply sumN_congr
          intro y hy
          rw [P.testBit_cmQ (by omega) hy, P.testBit_perpK hy hw]
          by_cases h1 : Qi c.val e.val p.val q.val y = 0 <;>
            by_cases h2 : Bi c.val p.val q.val y w = 0 <;> simp [h1, h2]
        rw [e1, colV_n0K hw, hsum]
      rw [hcol _ (ha i), hcol _ hbi, hN i hi]
    · rw [ttK_field _ _ _ (by omega) hi, ← (bidx_eq j (by omega)).1, ← (bidx_eq i hi).1,
        P.testBit_xwK (ha j) (ha i) ht, hB i hi j hj]
  have henc := c3Ext_sound ha hval 8 0 rfl hext
  apply List.ext_getElem (by rw [hl])
  intro i h1 h2
  have hi8 : i < 8 := by omega
  have hai : a i = bidx i := by
    have := fget_encF (w := 8) (fun j => ha j) 8 (7 - i) (by omega)
    have e : 8 - 1 - (7 - i) = i := by omega
    rw [henc, fget_BIDR i hi8, e] at this
    exact this.symm
  obtain ⟨hw, -, -, hpt⟩ := hwi i hi8
  rw [hbas i h2, ← hpt, hai]

end CFSG.KC.GMS.Snd

end
