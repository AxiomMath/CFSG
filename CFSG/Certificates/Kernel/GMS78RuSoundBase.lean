module

public import Certificates.Data.Kernel.GMS78Ru
public import CFSG.Certificates.Kernel.GMS78RuGen
public import Certificates.Data.GMS78RuNCoord

public section

namespace CFSG.KC.GMS.Snd

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl
theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl
theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl
theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by cases c <;> rfl
theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nat_xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nat_land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nat_lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nat_shiftLeft_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem nat_shiftRight_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_beq_eq (a b : Nat) : Nat.beq a b = (a == b) := rfl
theorem nat_blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · rw [← Bool.not_eq_true, Nat.blt_eq] at h; simp [h]
  · rw [Nat.blt_eq] at h; simp [h]
theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · rw [← Bool.not_eq_true, Nat.ble_eq] at h; simp [h]
  · rw [Nat.ble_eq] at h; simp [h]

theorem xor_cancel_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

macro "xsimp" : tactic =>
  `(tactic| simp only [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm, Nat.xor_self,
    xor_cancel_left, Nat.xor_zero, Nat.zero_xor])

macro "lomega" : tactic => `(tactic| ((try simp only [] at *) <;> omega))

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => simp [anyN]
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl (h' ▸ h)

theorem orN_testBit {n : Nat} {f : Nat → Nat} {j : Nat} :
    (orN n f).testBit j = true ↔ ∃ i < n, (f i).testBit j = true := by
  induction n with
  | zero => simp [orN]
  | succ n ih =>
    change (f n ||| orN n f).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl (h' ▸ h)

theorem xorN_succ (n : Nat) (f : Nat → Nat) : xorN (n + 1) f = f n ^^^ xorN n f := rfl
theorem xorN_zero (f : Nat → Nat) : xorN 0 f = 0 := rfl

theorem xorN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) : xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem xorN_xor (n : Nat) (f g : Nat → Nat) :
    xorN n (fun i => f i ^^^ g i) = xorN n f ^^^ xorN n g := by
  induction n with
  | zero => simp [xorN_zero]
  | succ n ih => rw [xorN_succ, xorN_succ, xorN_succ, ih]; xsimp

theorem xorN_lt {n w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

theorem xorN_map {n : Nat} {g : Nat → Nat} (f : Nat → Nat) (h0 : f 0 = 0)
    (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b) : f (xorN n g) = xorN n fun i => f (g i) := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [xorN_succ, xorN_succ, hadd, ih]

theorem foldK_succ (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldK (n + 1) f s = foldK n f (f n s) := by
  change strictN (f n s) (foldK n f) = _
  rw [strictN_eq]

theorem foldK_zero_state {n : Nat} {f : Nat → Nat → Nat} (h0 : ∀ k, f k 0 = 0) :
    foldK n f 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldK_succ, h0, ih]

theorem foldK_steps {f : Nat → Nat → Nat} {P : Nat → Nat → Prop} (h0 : ∀ k, f k 0 = 0)
    (hs : ∀ k s, f k s ≠ 0 → P k s) : ∀ n s, foldK n f s ≠ 0 → ∀ k < n, ∃ s', P k s'
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, s, h, k, hk => by
    rw [foldK_succ] at h
    have hn : f n s ≠ 0 := fun h' => h (by rw [h', foldK_zero_state h0])
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact foldK_steps h0 hs n _ h k hk
    · exact ⟨s, hs k s hn⟩

theorem orN_lt {n w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) : orN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    change f n ||| orN n f < 2 ^ w
    exact Nat.or_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

theorem lowBit_spec : ∀ w : Nat, w ≠ 0 → ∃ k, w &&& (w ^^^ (w - 1)) = 2 ^ k ∧
    w.testBit k = true ∧ ∀ i < k, w.testBit i = false
  | w, hw => by
    rcases Nat.mod_two_eq_zero_or_one w with he | ho
    · have hw2 : w / 2 ≠ 0 := by omega
      obtain ⟨k, hk1, hk2, hk3⟩ := lowBit_spec (w / 2) hw2
      refine ⟨k + 1, ?_, by rw [Nat.testBit_succ]; exact hk2, fun i hi => ?_⟩
      · apply Nat.eq_of_testBit_eq; intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_zero w]
          simp [he]
        | succ j =>
          have e1 : (w - 1) / 2 = w / 2 - 1 := by omega
          have h2 := congrArg (fun t => t.testBit j) hk1
          simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow] at h2
          rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_succ w,
            Nat.testBit_succ (w - 1), e1, h2]
          simp
      · cases i with
        | zero => simp [Nat.testBit_zero, he]
        | succ i => rw [Nat.testBit_succ]; exact hk3 i (by omega)
    · refine ⟨0, ?_, by simp [Nat.testBit_zero, ho], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      apply Nat.eq_of_testBit_eq; intro j
      cases j with
      | zero =>
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_zero w,
          Nat.testBit_zero (w - 1)]
        have : (w - 1) % 2 = 0 := by omega
        simp [ho, this]
      | succ j =>
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_succ w,
          Nat.testBit_succ (w - 1)]
        have : (w - 1) / 2 = w / 2 := by omega
        rw [this]; simp

theorem pop64_pow : ∀ k < 64, CFSG.KC.Local.pop64 (2 ^ k - 1) = k := by decide

@[expose] noncomputable def wAllF (f : Nat → Bool) (base n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => bIf(Nat.beq w (nat_lit 0), true,
      (fun low => bAnd(f (Nat.add base (CFSG.KC.Local.pop64 (Nat.sub low (nat_lit 1)))),
        ih (Nat.xor w low)))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1)))))) n

theorem wordAll_eq (f : Nat → Bool) (base : Nat) :
    CFSG.KC.Local.wordAll f base = wAllF f base 64 := rfl

theorem testBit_false_of_lt {w : Nat} (hw : w < 2 ^ 64) {k : Nat} (hk : 64 ≤ k) :
    w.testBit k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hk))

theorem wAllF_spec (f : Nat → Bool) (base : Nat) : ∀ n w, w < 2 ^ 64 →
    (∀ i < 64 - n, w.testBit i = false) → wAllF f base n w = true →
    ∀ k, w.testBit k = true → f (base + k) = true
  | 0, w, hw, hlow, _, k, hk => by
    by_cases h64 : k < 64
    · rw [hlow k (by omega)] at hk; exact absurd hk (by decide)
    · rw [testBit_false_of_lt hw (by omega)] at hk; exact absurd hk (by decide)
  | n + 1, w, hw, hlow, h, k, hk => by
    have hw0 : w ≠ 0 := by rintro rfl; simp at hk
    obtain ⟨k0, hl, hk0, hlt⟩ := lowBit_spec w hw0
    have hk064 : k0 < 64 := by
      by_contra hc; rw [testBit_false_of_lt hw (by omega)] at hk0; exact absurd hk0 (by decide)
    have hk0n : 64 - (n + 1) ≤ k0 := by
      by_contra hc; rw [hlow k0 (by omega)] at hk0; exact absurd hk0 (by decide)
    change bIf(Nat.beq w 0, true, (fun low => bAnd(f (Nat.add base
      (CFSG.KC.Local.pop64 (Nat.sub low 1))), wAllF f base n (Nat.xor w low)))
      (Nat.land w (Nat.xor w (Nat.sub w 1)))) = true at h
    simp only [bIf_eq, nat_beq_eq, nat_land_eq, nat_xor_eq, nat_sub_eq, nat_add_eq] at h
    have hb : (w == 0) = false := by simpa using hw0
    rw [hb, hl, pop64_pow k0 hk064] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have h' : f (base + k0) = true ∧ wAllF f base n (w ^^^ 2 ^ k0) = true := by
      split at h
      · exact ⟨by assumption, h⟩
      · exact absurd h (by decide)
    by_cases hkk : k = k0
    · rw [hkk]; exact h'.1
    · refine wAllF_spec f base n (w ^^^ 2 ^ k0)
        (Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by omega) hk064)) ?_ h'.2 k ?_
      · intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        rcases Nat.lt_or_ge i k0 with h1 | h1
        · rw [hlt i h1]; simp; omega
        · have : i = k0 := by omega
          rw [this, hk0]; simp
      · rw [Nat.testBit_xor, Nat.testBit_two_pow, hk]; simp; omega

theorem land_max (x : Nat) : x &&& 18446744073709551615 = x % 2 ^ 64 :=
  Nat.and_two_pow_sub_one_eq_mod x 64

theorem allBits_spec {n : Nat} {f : Nat → Bool} {M : Nat}
    (h : CFSG.KC.Local.allBits n f M = true) : ∀ k < n, M.testBit k = true → f k = true := by
  intro k hk hMk
  have outer : ∀ (M' J j₀ : Nat),
      Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun _ ih j => bAnd(CFSG.KC.Local.wordAll f (Nat.shiftLeft j (nat_lit 6))
          (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6)))
            (nat_lit 18446744073709551615)),
          ih (Nat.succ j))) J j₀ = true →
      ∀ j, j₀ ≤ j → j < j₀ + J → CFSG.KC.Local.wordAll f (j * 64)
        ((M' >>> (j * 64)) % 2 ^ 64) = true := by
    intro M' J
    induction J with
    | zero => intro j₀ _ j h1 h2; omega
    | succ J ih =>
      intro j₀ hJ j h1 h2
      change bAnd(_, _) = true at hJ
      rw [bAnd_eq, Bool.and_eq_true] at hJ
      rcases Nat.lt_or_ge j₀ j with h3 | h3
      · exact ih (j₀ + 1) hJ.2 j (by omega) (by omega)
      · have : j = j₀ := by omega
        subst this
        have := hJ.1
        simp only [nat_shiftLeft_eq, nat_shiftRight_eq, nat_land_eq, land_max,
          Nat.shiftLeft_eq] at this
        have e : (2 : Nat) ^ 6 = 64 := rfl
        rw [e] at this
        exact this
  have hw := outer _ _ 0 h (k / 64) (Nat.zero_le _) (by
    simp only [nat_shiftRight_eq, nat_add_eq, Nat.shiftRight_eq_div_pow]; norm_num; omega)
  rw [wordAll_eq] at hw
  have hk' := wAllF_spec f (k / 64 * 64) 64 _ (Nat.mod_lt _ (Nat.two_pow_pos 64)) (by simp) hw
    (k % 64) (by
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      simp only [nat_land_eq, nat_shiftLeft_eq, nat_sub_eq, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
      have : k / 64 * 64 + k % 64 = k := by omega
      rw [this]; simp [hk, hMk]; omega)
  have : k / 64 * 64 + k % 64 = k := by omega
  rwa [this] at hk'

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  simp [pw2, Nat.shiftLeft_eq]

theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  simp [maskN, pw2_eq]

theorem fget_eq (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  simp only [fget, maskN_eq, nat_land_eq, nat_shiftRight_eq, nat_mul_eq,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fget_lt (X i w : Nat) : fget X i w < 2 ^ w := by
  rw [fget_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem testBit_fget (X i w j : Nat) :
    (fget X i w).testBit j = (decide (j < w) && X.testBit (i * w + j)) := by
  simp only [fget, maskN_eq, nat_land_eq, nat_shiftRight_eq, nat_mul_eq, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem fget_xor (X Y i w : Nat) : fget (X ^^^ Y) i w = fget X i w ^^^ fget Y i w := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [testBit_fget, Nat.testBit_xor]
  cases decide (j < w) <;> simp

theorem fget_zero (i w : Nat) : fget 0 i w = 0 := by
  simp [fget_eq]

theorem fget_of_lt {X w : Nat} (h : X < 2 ^ w) : fget X 0 w = X := by
  rw [fget_eq]; simp [Nat.mod_eq_of_lt h]

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  simp only [bit, nat_land_eq, nat_shiftRight_eq, nat_beq_eq, Nat.and_one_is_mod,
    Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  cases h : X / 2 ^ i % 2 == 1 <;> simp_all

theorem bitN_eq (X i : Nat) : bitN X i = if X.testBit i then 1 else 0 := by
  simp only [bitN, nat_land_eq, nat_shiftRight_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> simp [h]

theorem eq_of_fget3 {v v' : Nat} (hv : v < 512) (hv' : v' < 512)
    (h0 : fget v 0 3 = fget v' 0 3) (h1 : fget v 1 3 = fget v' 1 3)
    (h2 : fget v 2 3 = fget v' 2 3) : v = v' := by
  simp only [fget_eq] at h0 h1 h2
  norm_num at h0 h1 h2
  omega

theorem fin8_xor_val (a b : Fin 8) : (a ^^^ b).val = a.val ^^^ b.val := by
  change (a.val ^^^ b.val) % 8 = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt)

theorem fin8_eq_iff (a b : Fin 8) : a = b ↔ a.val = b.val := Fin.ext_iff

theorem xor_lt8 {a b : Nat} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 :=
  Nat.xor_lt_two_pow (n := 3) ha hb

theorem m8_eq (a b : Nat) : m8 a b = fget MUL (8 * a + b) 3 := rfl

theorem m8_lt (a b : Nat) : m8 a b < 8 := fget_lt MUL _ 3

structure MulLaws : Prop where
  comm : ∀ a b, a < 8 → b < 8 → m8 a b = m8 b a
  dist : ∀ a b c, a < 8 → b < 8 → c < 8 → m8 a (b ^^^ c) = m8 a b ^^^ m8 a c

theorem mulLaws_of (h : mulOK = true) : MulLaws := by
  unfold mulOK at h
  simp only [allN_iff, andB_eq, Bool.and_eq_true, nat_beq_eq, beq_iff_eq, nat_xor_eq] at h
  exact ⟨fun a b ha hb => (h a ha b hb 0 (by omega)).1,
    fun a b c ha hb hc => (h a ha b hb c hc).2⟩

namespace MulLaws

variable (L : MulLaws)
include L

theorem zero_right {a : Nat} (ha : a < 8) : m8 a 0 = 0 := by
  have h := L.dist a 0 0 ha (by omega) (by omega)
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem zero_left {b : Nat} (hb : b < 8) : m8 0 b = 0 := by
  rw [L.comm 0 b (by omega) hb, L.zero_right hb]

theorem dist_left {a b c : Nat} (ha : a < 8) (hb : b < 8) (hc : c < 8) :
    m8 (a ^^^ b) c = m8 a c ^^^ m8 b c := by
  rw [L.comm _ c (xor_lt8 ha hb) hc, L.dist c a b hc ha hb, L.comm c a hc ha, L.comm c b hc hb]

theorem sq_add {a b : Nat} (ha : a < 8) (hb : b < 8) :
    m8 (a ^^^ b) (a ^^^ b) = m8 a a ^^^ m8 b b := by
  rw [L.dist_left ha hb (xor_lt8 ha hb), L.dist a a b ha ha hb, L.dist b a b hb ha hb,
    L.comm b a hb ha]
  xsimp

theorem quad_add {a b : Nat} (ha : a < 8) (hb : b < 8) :
    m8 (m8 (a ^^^ b) (a ^^^ b)) (m8 (a ^^^ b) (a ^^^ b)) =
      m8 (m8 a a) (m8 a a) ^^^ m8 (m8 b b) (m8 b b) := by
  rw [L.sq_add ha hb, L.sq_add (m8_lt a a) (m8_lt b b)]

end MulLaws

theorem sqC_eq (c e u r s : Nat) : sqC c e u r s =
    m8 (m8 (m8 u u) (m8 u u)) u ^^^ m8 c (m8 (m8 u r) (m8 u r)) ^^^ m8 (e ^^^ s) r := rfl

theorem commC_eq (c x1 x2 x3 z1 z2 z3 : Nat) : commC c x1 x2 x3 z1 z2 z3 =
    m8 x1 (m8 (m8 z1 z1) (m8 z1 z1)) ^^^ m8 (m8 (m8 x1 x1) (m8 x1 x1)) z1 ^^^
      m8 c (m8 (m8 x1 z2) (m8 x1 z2) ^^^ m8 (m8 z1 x2) (m8 z1 x2)) ^^^
      (m8 x3 z2 ^^^ m8 z3 x2) := rfl

theorem sqC_lt (c e u r s : Nat) : sqC c e u r s < 8 := by
  rw [sqC_eq]; exact xor_lt8 (xor_lt8 (m8_lt _ _) (m8_lt _ _)) (m8_lt _ _)

theorem commC_lt (c x1 x2 x3 z1 z2 z3 : Nat) : commC c x1 x2 x3 z1 z2 z3 < 8 := by
  rw [commC_eq]
  exact xor_lt8 (xor_lt8 (xor_lt8 (m8_lt _ _) (m8_lt _ _)) (m8_lt _ _))
    (xor_lt8 (m8_lt _ _) (m8_lt _ _))

namespace MulLaws

variable (L : MulLaws)
include L

theorem sqC_add {c e u r s u' r' s' : Nat} (hc : c < 8) (he : e < 8) (hu : u < 8) (hr : r < 8)
    (hs : s < 8) (hu' : u' < 8) (hr' : r' < 8) (hs' : s' < 8) :
    sqC c e (u ^^^ u') (r ^^^ r') (s ^^^ s') =
      sqC c e u r s ^^^ sqC c e u' r' s' ^^^ commC c u r s u' r' s' := by
  have h4 := L.quad_add hu hu'
  simp only [sqC_eq, commC_eq, h4]
  have hF := m8_lt (m8 u u) (m8 u u)
  have hF' := m8_lt (m8 u' u') (m8 u' u')
  rw [L.dist_left hF hF' (xor_lt8 hu hu'), L.dist _ u u' hF hu hu', L.dist _ u u' hF' hu hu',
    L.comm (m8 (m8 u' u') (m8 u' u')) u hF' hu]
  rw [L.dist_left hu hu' (xor_lt8 hr hr'), L.dist u r r' hu hr hr', L.dist u' r r' hu' hr hr']
  have ha := m8_lt u r
  have hb := m8_lt u r'
  have hc' := m8_lt u' r
  have hd := m8_lt u' r'
  rw [L.sq_add (xor_lt8 ha hb) (xor_lt8 hc' hd), L.sq_add ha hb, L.sq_add hc' hd]
  rw [L.dist c _ _ hc (xor_lt8 (m8_lt _ _) (m8_lt _ _)) (xor_lt8 (m8_lt _ _) (m8_lt _ _)),
    L.dist c _ _ hc (m8_lt _ _) (m8_lt _ _), L.dist c _ _ hc (m8_lt _ _) (m8_lt _ _),
    L.dist c _ _ hc (m8_lt _ _) (m8_lt _ _)]
  rw [← Nat.xor_assoc e s s', L.dist_left (xor_lt8 he hs) hs' (xor_lt8 hr hr'),
    L.dist _ r r' (xor_lt8 he hs) hr hr', L.dist s' r r' hs' hr hr',
    L.dist_left he hs hr', L.dist_left he hs' hr']
  xsimp

theorem sqC_zero {c e : Nat} (hc : c < 8) (he : e < 8) : sqC c e 0 0 0 = 0 := by
  have h0 : m8 0 0 = 0 := L.zero_right (by omega)
  simp only [sqC_eq, h0, Nat.xor_zero, L.zero_right hc, L.zero_right he]

theorem commC_add {c x1 x2 x3 y1 y2 y3 z1 z2 z3 : Nat} (hc : c < 8) (hx1 : x1 < 8) (hx2 : x2 < 8)
    (hx3 : x3 < 8) (hy1 : y1 < 8) (hy2 : y2 < 8) (hy3 : y3 < 8) (hz1 : z1 < 8) (hz2 : z2 < 8)
    (hz3 : z3 < 8) :
    commC c (x1 ^^^ y1) (x2 ^^^ y2) (x3 ^^^ y3) z1 z2 z3 =
      commC c x1 x2 x3 z1 z2 z3 ^^^ commC c y1 y2 y3 z1 z2 z3 := by
  simp only [commC_eq, L.quad_add hx1 hy1]
  have hZ := m8_lt (m8 z1 z1) (m8 z1 z1)
  rw [L.dist_left hx1 hy1 hZ, L.dist_left (m8_lt _ _) (m8_lt _ _) hz1, L.dist_left hx1 hy1 hz2,
    L.dist z1 x2 y2 hz1 hx2 hy2, L.sq_add (m8_lt _ _) (m8_lt _ _),
    L.sq_add (m8_lt _ _) (m8_lt _ _), L.dist_left hx3 hy3 hz2, L.dist z3 x2 y2 hz3 hx2 hy2]
  simp only [L.dist c, hc, m8_lt, xor_lt8]
  xsimp

theorem commC_symm {c x1 x2 x3 z1 z2 z3 : Nat} (hx1 : x1 < 8) (hz1 : z1 < 8) :
    commC c x1 x2 x3 z1 z2 z3 = commC c z1 z2 z3 x1 x2 x3 := by
  rw [commC_eq, commC_eq, L.comm x1 _ hx1 (m8_lt _ _), L.comm _ z1 (m8_lt _ _) hz1]
  xsimp

theorem commC_self {c e x1 x2 x3 : Nat} (hc : c < 8) (he : e < 8) (hx1 : x1 < 8) (hx2 : x2 < 8)
    (hx3 : x3 < 8) : commC c x1 x2 x3 x1 x2 x3 = 0 := by
  have h := L.sqC_add hc he hx1 hx2 hx3 hx1 hx2 hx3
  rw [Nat.xor_self, Nat.xor_self, Nat.xor_self, L.sqC_zero hc he, Nat.xor_self, Nat.zero_xor] at h
  exact h.symm

end MulLaws

theorem fget3_lt (X i : Nat) : fget X i 3 < 8 := fget_lt X i 3

theorem sqK_eq (c e v : Nat) : sqK c e v = sqC c e (fget v 0 3) (fget v 1 3) (fget v 2 3) := rfl

theorem commK_eq (c x z : Nat) : commK c x z =
    commC c (fget x 0 3) (fget x 1 3) (fget x 2 3) (fget z 0 3) (fget z 1 3) (fget z 2 3) := rfl

theorem sqK_lt (c e v : Nat) : sqK c e v < 8 := sqC_lt _ _ _ _ _

theorem commK_lt (c x z : Nat) : commK c x z < 8 := commC_lt _ _ _ _ _ _ _

namespace MulLaws

variable (L : MulLaws)
include L

theorem sqK_xor {c e : Nat} (hc : c < 8) (he : e < 8) (x y : Nat) :
    sqK c e (x ^^^ y) = sqK c e x ^^^ sqK c e y ^^^ commK c x y := by
  simp only [sqK_eq, commK_eq, fget_xor]
  exact L.sqC_add hc he (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _)
    (fget3_lt _ _) (fget3_lt _ _)

theorem sqK_zero {c e : Nat} (hc : c < 8) (he : e < 8) : sqK c e 0 = 0 := by
  simp only [sqK_eq, fget_zero]; exact L.sqC_zero hc he

theorem commK_xor {c : Nat} (hc : c < 8) (x y z : Nat) :
    commK c (x ^^^ y) z = commK c x z ^^^ commK c y z := by
  simp only [commK_eq, fget_xor]
  exact L.commC_add hc (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _)
    (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _)

theorem commK_symm (c x z : Nat) : commK c x z = commK c z x := by
  simp only [commK_eq]; exact L.commC_symm (fget3_lt _ _) (fget3_lt _ _)

theorem commK_self {c : Nat} (hc : c < 8) (x : Nat) : commK c x x = 0 := by
  simp only [commK_eq]
  exact L.commC_self (e := 0) hc (by omega) (fget3_lt _ _) (fget3_lt _ _) (fget3_lt _ _)

theorem commK_zero {c : Nat} (hc : c < 8) (z : Nat) : commK c 0 z = 0 := by
  have h := L.commK_xor hc 0 0 z
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem commK_xor_right {c : Nat} (hc : c < 8) (x y z : Nat) :
    commK c x (y ^^^ z) = commK c x y ^^^ commK c x z := by
  rw [L.commK_symm, L.commK_xor hc, L.commK_symm c y, L.commK_symm c z]

end MulLaws

theorem or_shift3 {a b c : Nat} (ha : a < 8) (hb : b < 8) :
    a ||| (b <<< 3 ||| c <<< 6) = a + 8 * b + 64 * c := by
  have h1 : b <<< 3 ||| c <<< 6 = (b ||| c <<< 3) <<< 3 := by
    rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq c 3, Nat.shiftLeft_eq (c * 2 ^ 3) 3,
      Nat.shiftLeft_eq c 6, Nat.mul_assoc]
  have h2 : b ||| c <<< 3 = c <<< 3 + b := by
    rw [Nat.or_comm, Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  rw [h1, h2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 3) (by omega)]
  simp only [Nat.shiftLeft_eq]
  omega

theorem packV_eq (x : V3) : packV x = x.1.val + 8 * x.2.1.val + 64 * x.2.2.val := by
  obtain ⟨u, r, s⟩ := x
  exact or_shift3 u.isLt r.isLt

theorem packV_lt (x : V3) : packV x < 512 := by
  rw [packV_eq]; have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt; omega

theorem fget_packV0 (x : V3) : fget (packV x) 0 3 = x.1.val := by
  rw [packV_eq, fget_eq]; have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
  norm_num; omega
theorem fget_packV1 (x : V3) : fget (packV x) 1 3 = x.2.1.val := by
  rw [packV_eq, fget_eq]; have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
  norm_num; omega
theorem fget_packV2 (x : V3) : fget (packV x) 2 3 = x.2.2.val := by
  rw [packV_eq, fget_eq]; have := x.1.isLt; have := x.2.1.isLt; have := x.2.2.isLt
  norm_num; omega

theorem packV_inj {x y : V3} (h : packV x = packV y) : x = y := by
  have h0 := fget_packV0 x; have h1 := fget_packV1 x; have h2 := fget_packV2 x
  rw [h] at h0 h1 h2
  rw [fget_packV0] at h0; rw [fget_packV1] at h1; rw [fget_packV2] at h2
  obtain ⟨u, r, s⟩ := x; obtain ⟨u', r', s'⟩ := y
  simp only at h0 h1 h2
  rw [Fin.ext h0, Fin.ext h1, Fin.ext h2]

theorem packV_addV (x y : V3) : packV (addV x y) = packV x ^^^ packV y := by
  apply eq_of_fget3 (packV_lt _) (Nat.xor_lt_two_pow (n := 9) (packV_lt x) (packV_lt y))
  all_goals simp only [fget_xor, fget_packV0, fget_packV1, fget_packV2, addV, fin8_xor_val]

theorem sqK_packV (c e : Nat) (x : V3) :
    sqK c e (packV x) = sqC c e x.1.val x.2.1.val x.2.2.val := by
  rw [sqK_eq, fget_packV0, fget_packV1, fget_packV2]

theorem commK_packV (c : Nat) (x z : V3) :
    commK c (packV x) (packV z) =
      commC c x.1.val x.2.1.val x.2.2.val z.1.val z.2.1.val z.2.2.val := by
  rw [commK_eq, fget_packV0, fget_packV1, fget_packV2, fget_packV0, fget_packV1, fget_packV2]

theorem bindRec_spec {α : Type} {g : α → Nat → Bool} {T w n : Nat} :
    ∀ (L : List α) (i₀ : Nat),
      List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
        (fun a _ ih i => andB (g a (fget T i w)) (ih (Nat.succ i))) L i₀ = true →
      i₀ + L.length = n ∧ ∀ k (hk : k < L.length), g L[k] (fget T (i₀ + k) w) = true
  | [], i₀, h => by
    simp only [nat_beq_eq, beq_iff_eq] at h
    exact ⟨by simpa using h, fun k hk => absurd hk (by simp)⟩
  | a :: L, i₀, h => by
    change andB (g a (fget T i₀ w)) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := bindRec_spec L (i₀ + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk => ?_⟩
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := h2 k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [← Nat.add_assoc, Nat.add_right_comm]; exact this

theorem bindList_spec {α : Type} {f : α → Nat} {T w n : Nat} :
    ∀ (L : List α) (i₀ : Nat),
      List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
        (fun a _ ih i => andB (Nat.beq (f a) (fget T i w)) (ih (Nat.succ i))) L i₀ = true →
      i₀ + L.length = n ∧ ∀ k (hk : k < L.length), f L[k] = fget T (i₀ + k) w
  | [], i₀, h => by
    simp only [nat_beq_eq, beq_iff_eq] at h
    exact ⟨by simpa using h, fun k hk => absurd hk (by simp)⟩
  | a :: L, i₀, h => by
    change andB (Nat.beq (f a) (fget T i₀ w)) _ = true at h
    rw [andB_eq, Bool.and_eq_true, nat_beq_eq, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := bindList_spec L (i₀ + 1) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk => ?_⟩
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := h2 k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [this]; congr 1; omega

theorem bindList_iff {α : Type} {f : α → Nat} {L : List α} {T w n : Nat}
    (h : bindList f L T w n = true) :
    L.length = n ∧ ∀ k (hk : k < L.length), f L[k] = fget T k w := by
  obtain ⟨h1, h2⟩ := bindList_spec (f := f) (T := T) (w := w) (n := n) L 0 h
  exact ⟨by omega, fun k hk => by rw [h2 k hk, Nat.zero_add]⟩

theorem bindFin8_iff {L : List (Fin 8)} {T n : Nat} (h : bindFin8 L T n = true) :
    L.length = n ∧ ∀ k (hk : k < L.length), (L[k]).val = fget T k 3 := by
  obtain ⟨h1, h2⟩ := bindList_spec (f := fun a : Fin 8 => a.val) (T := T) (w := 3) (n := n) L 0 h
  exact ⟨by omega, fun k hk => by rw [h2 k hk, Nat.zero_add]⟩

theorem mul8_val {mt : Array (Fin 8)} (hM : bindMul mt = true) (a b : Fin 8) :
    (Gen.mul8 mt a b).val = m8 a.val b.val := by
  obtain ⟨hl, hk⟩ := bindFin8_iff hM
  have hlt : 8 * a.val + b.val < mt.toList.length := by
    rw [hl]; change _ < 64; have := a.isLt; have := b.isLt; omega
  have hs : 8 * a.val + b.val < mt.size := by rw [← Array.length_toList]; exact hlt
  have := hk _ hlt
  simp only [Gen.mul8, Array.getD, hs, dite_true]
  rw [Array.getElem_toList] at this
  rw [m8_eq]
  exact this

theorem sqN_val {mt : Array (Fin 8)} (hM : bindMul mt = true) (c e : Fin 8) (x : V3) :
    (Gen.sqN mt c e x).val = sqC c.val e.val x.1.val x.2.1.val x.2.2.val := by
  simp only [Gen.sqN, fin8_xor_val, mul8_val hM, sqC_eq]

theorem commN_val {mt : Array (Fin 8)} (hM : bindMul mt = true) (c : Fin 8) (x z : V3) :
    (Gen.commN mt c x z).val =
      commC c.val x.1.val x.2.1.val x.2.2.val z.1.val z.2.1.val z.2.2.val := by
  simp only [Gen.commN, fin8_xor_val, mul8_val hM, commC_eq, Nat.xor_assoc]

theorem sqN_packV {mt : Array (Fin 8)} (hM : bindMul mt = true) (c e : Fin 8) (x : V3) :
    (Gen.sqN mt c e x).val = sqK c.val e.val (packV x) := by
  rw [sqN_val hM, sqK_packV]

theorem commN_packV {mt : Array (Fin 8)} (hM : bindMul mt = true) (c : Fin 8) (x z : V3) :
    (Gen.commN mt c x z).val = commK c.val (packV x) (packV z) := by
  rw [commN_val hM, commK_packV]

theorem lor_shift {a k : Nat} (b : Nat) (ha : a < 2 ^ k) : a ||| b <<< k = a + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.mul_comm]

theorem fget_fget {R w i v : Nat} (h : i * v + v ≤ w) : fget (fget R 0 w) i v = fget R i v := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [testBit_fget, Nat.zero_mul, Nat.zero_add]
  by_cases hj : j < v
  · have : i * v + j < w := by omega
    simp [hj, this]
  · simp [hj]

theorem pack4_eq (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) :
    pack4 t = t.1.val + 8 * t.2.1.val + 64 * t.2.2.1.val + 512 * t.2.2.2.val := by
  obtain ⟨c, e, p, q⟩ := t
  have hc := c.isLt; have he := e.isLt; have hp := p.isLt; have hq := q.isLt
  change (c.val ||| e.val <<< 3) ||| (p.val <<< 6 ||| q.val <<< 9) = _
  have h1 : c.val ||| e.val <<< 3 = c.val + 8 * e.val := lor_shift (k := 3) _ hc
  have h2 : p.val <<< 6 ||| q.val <<< 9 = (p.val ||| q.val <<< 3) <<< 6 := by
    rw [Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq q.val 3,
      Nat.shiftLeft_eq (q.val * 2 ^ 3) 6, Nat.shiftLeft_eq q.val 9, Nat.mul_assoc]
  rw [h1, h2, lor_shift (k := 3) _ hp, lor_shift (k := 6) _ (by omega)]
  norm_num
  omega

theorem fget_pack4 (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) :
    fget (pack4 t) 0 3 = t.1.val ∧ fget (pack4 t) 1 3 = t.2.1.val ∧
      fget (pack4 t) 2 3 = t.2.2.1.val ∧ fget (pack4 t) 3 3 = t.2.2.2.val := by
  rw [pack4_eq]
  have := t.1.isLt; have := t.2.1.isLt; have := t.2.2.1.isLt; have := t.2.2.2.isLt
  simp only [fget_eq]
  norm_num
  omega

theorem pack4_inj {t t' : Fin 8 × Fin 8 × Fin 8 × Fin 8} (h : pack4 t = pack4 t') : t = t' := by
  rw [pack4_eq, pack4_eq] at h
  obtain ⟨c, e, p, q⟩ := t; obtain ⟨c', e', p', q'⟩ := t'
  simp only at h
  have := c.isLt; have := e.isLt; have := p.isLt; have := q.isLt
  have := c'.isLt; have := e'.isLt; have := p'.isLt; have := q'.isLt
  have h1 : c = c' := Fin.ext (by omega)
  have h2 : e = e' := Fin.ext (by omega)
  have h3 : p = p' := Fin.ext (by omega)
  have h4 : q = q' := Fin.ext (by omega)
  rw [h1, h2, h3, h4]

theorem packV_zero : packV ((0, 0, 0) : V3) = 0 := by rw [packV_eq]; rfl

theorem packV_selV (b : Bool) (v : V3) : packV (selV b v) = if b then packV v else 0 := by
  cases b <;> simp [selV, packV_zero]

theorem xiK_eq {Xi : List V3} {XI : Nat} (hl : Xi.length = 8)
    (hb : ∀ k (hk : k < Xi.length), packV Xi[k] = fget XI k 9) (m : Nat) :
    xiK XI m = packV (xiApply Xi m) := by
  have e : ∀ j, j < 8 → packV (Xi.getD j (0, 0, 0)) = fget XI j 9 := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by omega), hb j (by omega)]
  simp only [xiK, xorN_succ, xorN_zero, nIf_eq, bit_eq, xiApply, packV_addV, packV_selV,
    Nat.xor_zero]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  xsimp

theorem allLt_spec : ∀ (X : List Nat),
    List.rec (motive := fun _ => Bool) true (fun n _ ih => andB (Nat.blt n (nat_lit 256)) ih) X =
      true → ∀ n ∈ X, n < 256
  | [], _ => by simp
  | a :: X, h => by
    change andB (Nat.blt a 256) _ = true at h
    rw [andB_eq, Bool.and_eq_true, nat_blt_eq, decide_eq_true_eq] at h
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h.1
    · exact allLt_spec X h.2 n hn

theorem sdRec_spec {t : Fin 8 × Fin 8 × Fin 8 × Fin 8} {X : List Nat} {Xi : List V3} {R : Nat}
    (h : sdRecOK (t, X, Xi) R = true) :
    pack4 t = fget R 0 12 ∧ X.length = 8 ∧ (∀ k (hk : k < X.length), X[k] = fget (R >>> 12) k 8) ∧
      (∀ n ∈ X, n < 256) ∧ Xi.length = 8 ∧
      ∀ k (hk : k < Xi.length), packV Xi[k] = fget (R >>> 76) k 9 := by
  change andB (Nat.beq (pack4 t) (fget R 0 12)) (andB (bindList (fun n => n) X (R >>> 12) 8 8)
    (andB (List.rec (motive := fun _ => Bool) true (fun n _ ih => andB (Nat.blt n (nat_lit 256)) ih)
      X) (bindList packV Xi (R >>> 76) 9 8))) = true at h
  simp only [andB_eq, Bool.and_eq_true, nat_beq_eq, beq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h2a, h2b⟩ := bindList_iff h2
  obtain ⟨h4a, h4b⟩ := bindList_iff h4
  exact ⟨h1, h2a, h2b, allLt_spec X h3, h4a, h4b⟩

theorem bindSD_spec {sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)} {SD : Nat}
    (h : bindSD sd SD = true) :
    sd.length = 7 ∧ ∀ k (hk : k < sd.length), sdRecOK sd[k] (fget SD k 160) = true := by
  obtain ⟨h1, h2⟩ := bindRec_spec (g := sdRecOK) (T := SD) (w := 160) (n := 7) sd 0 h
  exact ⟨by omega, fun k hk => by have := h2 k hk; rwa [Nat.zero_add] at this⟩

theorem fget_rec {t : Fin 8 × Fin 8 × Fin 8 × Fin 8} {R : Nat} (h : pack4 t = fget R 0 12) :
    fget R 0 3 = t.1.val ∧ fget R 1 3 = t.2.1.val ∧ fget R 2 3 = t.2.2.1.val ∧
      fget R 3 3 = t.2.2.2.val := by
  obtain ⟨h0, h1, h2, h3⟩ := fget_pack4 t
  rw [h, fget_fget (by omega)] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem land7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
theorem land3 (x : Nat) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

theorem lamK_eq (p q t : Nat) :
    lamK p q t = (if t.testBit 0 then p else 0) ^^^ (if t.testBit 1 then q else 0) := by
  simp only [lamK, nIf_eq, bit_eq, nat_xor_eq]

theorem lamK_lt {p q : Nat} (hp : p < 8) (hq : q < 8) (t : Nat) : lamK p q t < 8 := by
  rw [lamK_eq]; split <;> split <;> simp [hp, hq, xor_lt8]

theorem lamK_xor (p q t t' : Nat) : lamK p q (t ^^^ t') = lamK p q t ^^^ lamK p q t' := by
  simp only [lamK_eq, Nat.testBit_xor]
  cases t.testBit 0 <;> cases t'.testBit 0 <;> cases t.testBit 1 <;> cases t'.testBit 1 <;>
    simp [Nat.xor_comm]

theorem wK_eq {p q i : Nat} (hi : i < 256) :
    wK p q i = i / 32 + 8 * (i / 4 % 8) + 64 * lamK p q (i % 4) := by
  simp only [wK, nat_lor_eq, nat_shiftRight_eq, nat_shiftLeft_eq, nat_land_eq, land7, land3,
    Nat.or_assoc, Nat.shiftRight_eq_div_pow]
  rw [or_shift3 (by omega) (by omega)]

theorem wK_lt {p q i : Nat} (hp : p < 8) (hq : q < 8) (hi : i < 256) : wK p q i < 512 := by
  rw [wK_eq hi]; have := lamK_lt hp hq (i % 4); omega

theorem fget_add3 {a b c : Nat} (ha : a < 8) (hb : b < 8) (hc : c < 8) :
    fget (a + 8 * b + 64 * c) 0 3 = a ∧ fget (a + 8 * b + 64 * c) 1 3 = b ∧
      fget (a + 8 * b + 64 * c) 2 3 = c := by
  simp only [fget_eq]
  norm_num
  omega

theorem fget_wK0 {p q i : Nat} (hp : p < 8) (hq : q < 8) (hi : i < 256) :
    fget (wK p q i) 0 3 = i / 32 := by
  rw [wK_eq hi]
  exact (fget_add3 (by omega) (by omega) (lamK_lt hp hq _)).1
theorem fget_wK1 {p q i : Nat} (hp : p < 8) (hq : q < 8) (hi : i < 256) :
    fget (wK p q i) 1 3 = i / 4 % 8 := by
  rw [wK_eq hi]
  exact (fget_add3 (by omega) (by omega) (lamK_lt hp hq _)).2.1
theorem fget_wK2 {p q i : Nat} (hp : p < 8) (hq : q < 8) (hi : i < 256) :
    fget (wK p q i) 2 3 = lamK p q (i % 4) := by
  rw [wK_eq hi]
  exact (fget_add3 (by omega) (by omega) (lamK_lt hp hq _)).2.2

@[expose] def lamF (p q : Fin 8) (t : Nat) : Fin 8 :=
  (if t.testBit 0 then p else 0) ^^^ (if t.testBit 1 then q else 0)

@[expose] def wPt (p q : Fin 8) (i : Nat) : V3 :=
  (⟨i / 32 % 8, Nat.mod_lt _ (by omega)⟩, ⟨i / 4 % 8, Nat.mod_lt _ (by omega)⟩, lamF p q (i % 4))

theorem lamF_val (p q : Fin 8) (t : Nat) : (lamF p q t).val = lamK p.val q.val t := by
  rw [lamF, fin8_xor_val, lamK_eq]
  split <;> split <;> rfl

theorem fin8_xor_zero (a : Fin 8) : a ^^^ 0 = a := Fin.ext (by rw [fin8_xor_val]; simp)
theorem fin8_zero_xor (a : Fin 8) : 0 ^^^ a = a := Fin.ext (by rw [fin8_xor_val]; simp)

theorem lamF_0 (p q : Fin 8) : lamF p q 0 = 0 := by
  simp [lamF, (by decide : Nat.testBit 0 0 = false), (by decide : Nat.testBit 0 1 = false)]
theorem lamF_1 (p q : Fin 8) : lamF p q 1 = p := by
  simp [lamF, (by decide : Nat.testBit 1 0 = true), (by decide : Nat.testBit 1 1 = false)]
theorem lamF_2 (p q : Fin 8) : lamF p q 2 = q := by
  simp [lamF, (by decide : Nat.testBit 2 0 = false), (by decide : Nat.testBit 2 1 = true),
    fin8_zero_xor]
theorem lamF_3 (p q : Fin 8) : lamF p q 3 = p ^^^ q := by
  simp [lamF, (by decide : Nat.testBit 3 0 = true), (by decide : Nat.testBit 3 1 = true)]

theorem lamF_cases (p q : Fin 8) {t : Nat} (ht : t < 4) :
    (t = 0 ∧ lamF p q t = 0) ∨ (t = 1 ∧ lamF p q t = p) ∨ (t = 2 ∧ lamF p q t = q) ∨
      (t = 3 ∧ lamF p q t = p ^^^ q) := by
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, lamF_0 p q⟩
  · exact Or.inr (Or.inl ⟨rfl, lamF_1 p q⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, lamF_2 p q⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, lamF_3 p q⟩))

theorem lamF_mem (p q : Fin 8) {t : Nat} (ht : t < 4) : lamF p q t ∈ lamList p q := by
  rcases lamF_cases p q ht with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h, lamList]

theorem packV_wPt (p q : Fin 8) {i : Nat} (hi : i < 256) :
    packV (wPt p q i) = wK p.val q.val i := by
  rw [packV_eq, wK_eq hi]
  simp only [wPt, lamF_val]
  omega

theorem mem_wList {p q : Fin 8} {x : V3} : x ∈ wList p q ↔ x.2.2 ∈ lamList p q := by
  obtain ⟨u, r, s⟩ := x
  simp [wList, all8, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem wPt_mem (p q : Fin 8) {i : Nat} : wPt p q i ∈ wList p q :=
  mem_wList.mpr (lamF_mem p q (Nat.mod_lt _ (by omega)))

theorem exists_wPt {p q : Fin 8} {x : V3} (hx : x ∈ wList p q) :
    ∃ i < 256, wPt p q i = x := by
  obtain ⟨u, r, s⟩ := x
  have hs := mem_wList.mp hx
  simp only [lamList, List.mem_cons, List.not_mem_nil, or_false] at hs
  have key : ∃ t < 4, lamF p q t = s := by
    rcases hs with h | h | h | h
    · exact ⟨0, by omega, by rw [lamF_0, h]⟩
    · exact ⟨1, by omega, by rw [lamF_1, h]⟩
    · exact ⟨2, by omega, by rw [lamF_2, h]⟩
    · exact ⟨3, by omega, by rw [lamF_3, h]⟩
  obtain ⟨t, ht, hts⟩ := key
  refine ⟨32 * u.val + 4 * r.val + t, by have := u.isLt; have := r.isLt; omega, ?_⟩
  have hu := u.isLt; have hr := r.isLt
  simp only [wPt]
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) ?_)
  · simp only; omega
  · simp only; omega
  · simp only
    rw [← hts]; congr 1; omega

theorem lineK_eq (p q l : Nat) : lineK p q l =
    if l < 8 then l else if l < 16 then (l - 8) <<< 3 else lamK p q (l - 16) <<< 6 := by
  simp only [lineK, nIf_eq, nat_blt_eq, decide_eq_true_eq, nat_sub_eq, nat_shiftLeft_eq]

theorem lineK_mem (p q : Fin 8) {l : Nat} (hl : l < 20) :
    ∃ z ∈ lineList p q, packV z = lineK p.val q.val l := by
  rw [lineK_eq]
  by_cases h8 : l < 8
  · refine ⟨(⟨l, h8⟩, 0, 0), by simp [lineList, all8, List.mem_finRange], ?_⟩
    simp only [h8, ↓reduceIte, packV_eq]; rfl
  · by_cases h16 : l < 16
    · refine ⟨(0, ⟨l - 8, by omega⟩, 0), by simp [lineList, all8, List.mem_finRange], ?_⟩
      simp only [h8, h16, ↓reduceIte, packV_eq, Nat.shiftLeft_eq]; simp; omega
    · refine ⟨(0, 0, lamF p q (l - 16)), ?_, ?_⟩
      · simp only [lineList, List.mem_append, List.mem_map]
        exact Or.inr ⟨_, lamF_mem p q (by omega), rfl⟩
      · simp only [h8, h16, ↓reduceIte, packV_eq, Nat.shiftLeft_eq, lamF_val]; simp; omega

theorem fin_beq_val {n : Nat} (a b : Fin n) : (a == b) = (a.val == b.val) := by
  rw [Bool.eq_iff_iff]; simp [Fin.ext_iff]

theorem indep3_eq (a b c : Fin 8) : indep3 a b c = indep3K a.val b.val c.val := by
  simp only [indep3, indep3K, andB_eq, notB_eq, nat_beq_eq, nat_xor_eq, bne, fin_beq_val,
    fin8_xor_val, Bool.and_assoc]
  rfl

theorem indep3K_spec {a b c : Nat} (h : indep3K a b c = true) : a ≠ 0 ∧ b ≠ 0 ∧ b ≠ a := by
  simp only [indep3K, andB_eq, notB_eq, nat_beq_eq, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem c1Need_iff (c e v : Nat) :
    c1Need c e v = true ↔ fget v 0 3 ≠ 0 ∧ fget v 1 3 ≠ 0 ∧ sqK c e v = 0 := by
  simp only [c1Need, andB_eq, notB_eq, nat_beq_eq, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]

theorem c1Wit_spec {c e p q x w : Nat} (h : c1Wit c e p q x w = true) :
    commK c x (wK p q (fget w 0 8)) = 0 ∧ commK c x (wK p q (fget w 1 8)) = 0 ∧
      commK c x (wK p q (fget w 2 8)) = 0 ∧
      indep3K (sqK c e (wK p q (fget w 0 8))) (sqK c e (wK p q (fget w 1 8)))
        (sqK c e (wK p q (fget w 2 8))) = true := by
  simp only [c1Wit, andB_eq, nat_beq_eq, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem c1Step_zero (c e p q WS k : Nat) : c1Step c e p q WS k 0 = 0 := rfl

theorem c1Step_spec {c e p q WS k s : Nat} (h : c1Step c e p q WS k s ≠ 0) :
    c1Need c e (wK p q k) = true → c1Wit c e p q (wK p q k) (fget WS (s - 1) 24) = true := by
  intro hn
  simp only [c1Step, nIf_eq, nat_sub_eq] at h
  rw [hn] at h
  by_contra hw
  simp only [Bool.not_eq_true] at hw
  rw [hw] at h
  simp at h

theorem allNZK_packV (x : V3) : allNZK (packV x) = allNZ x := by
  simp only [allNZK, allNZ, andB_eq, notB_eq, nat_beq_eq, fget_packV0, fget_packV1, fget_packV2,
    bne, fin_beq_val, Bool.and_assoc]
  rfl

theorem rec01_beq (a b : Bool) :
    Nat.beq (Bool.rec (motive := fun _ => Nat) 0 1 a) (Bool.rec (motive := fun _ => Nat) 0 1 b) =
      (a == b) := by
  cases a <;> cases b <;> rfl

theorem rec01_eq_one (a : Bool) : Nat.beq (Bool.rec (motive := fun _ => Nat) 0 1 a) 1 = a := by
  cases a <;> rfl

theorem specK_spec {sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)} (hS : bindSpec sl = true)
    {t : Fin 8 × Fin 8 × Fin 8 × Fin 8}
    (h : specK t.1.val t.2.1.val t.2.2.1.val t.2.2.2.val = true) : sl.contains t = true := by
  obtain ⟨hl, hk⟩ := bindList_iff hS
  unfold specK at h
  rw [anyN_iff] at h
  obtain ⟨k, hk7, hk'⟩ := h
  rw [nat_beq_eq, beq_iff_eq] at hk'
  have hkl : k < sl.length := by lomega
  have e : pack4 sl[k] = pack4 t := by
    rw [hk k hkl, hk']
    obtain ⟨c, e, p, q⟩ := t
    rfl
  rw [List.contains_iff_mem, ← pack4_inj e]
  exact List.getElem_mem _

theorem zMask_testBit {c e p q i : Nat} :
    (zMask c e p q).testBit i = true ↔
      i < 256 ∧ allNZK (wK p q i) = true ∧ sqK c e (wK p q i) = 0 := by
  unfold zMask
  rw [orN_testBit]
  constructor
  · rintro ⟨i', hi', h⟩
    simp only [nIf_eq, andB_eq, nat_beq_eq, Bool.and_eq_true, beq_iff_eq, nat_shiftLeft_eq] at h
    split at h
    · rename_i hc
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at h
      have : i' = i := by simpa using h
      subst this
      exact ⟨hi', hc⟩
    · simp at h
  · rintro ⟨hi, h1, h2⟩
    refine ⟨i, hi, ?_⟩
    simp only [nIf_eq, andB_eq, nat_beq_eq, Bool.and_eq_true, beq_iff_eq, nat_shiftLeft_eq,
      h1, h2, and_self, ↓reduceIte, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    simp

theorem c2Inner_spec {c e p q : Nat} (h : c2Inner c e p q = true) :
    ∀ i < 256, ∀ j < 256, (zMask c e p q).testBit i = true → (zMask c e p q).testBit j = true →
      c2Pair c p q (wK p q i) (wK p q j) = true := by
  unfold c2Inner at h
  rw [strictN_eq, rec01_eq_one] at h
  intro i hi j hj hzi hzj
  exact allBits_spec (allBits_spec h i hi hzi) j hj hzj

theorem c2Pair_spec {c p q x y : Nat} (h : c2Pair c p q x y = true) :
    x = y ∨ commK c x y ≠ 0 ∨ allNZK (x ^^^ y) = false ∨
      ∃ l < 20, (commK c x (lineK p q l) = 0) ≠ (commK c y (lineK p q l) = 0) := by
  simp only [c2Pair, rec01_beq] at h
  simp only [orB_eq, notB_eq, nat_beq_eq, nat_xor_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, anyN_iff] at h
  rcases h with h | h | h | ⟨l, hl, hl'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ⟨l, hl, fun e => hl' ?_⟩))
    rw [Bool.eq_iff_iff]; simpa using e

theorem canonK_eq (p q : Nat) :
    canonK p q = (decide (0 < p) && decide (p < q) && decide (q < p ^^^ q)) := by
  simp only [canonK, andB_eq, nat_blt_eq, nat_xor_eq, Bool.and_assoc]

theorem canon_eq (p q : Fin 8) : canon p q = canonK p.val q.val := by
  rw [canonK_eq, canon, fin8_xor_val]

theorem pairP_lt (k : Nat) : pairP k < 8 := fget3_lt _ _
theorem pairQ_lt (k : Nat) : pairQ k < 8 := fget3_lt _ _

theorem pairsOK_spec (h : pairsOK = true) {p q : Nat} (hp : p < 8) (hq : q < 8)
    (hc : canonK p q = true) : ∃ k < 7, pairP k = p ∧ pairQ k = q := by
  unfold pairsOK at h
  rw [allN_iff] at h
  have h' := h p hp
  rw [allN_iff] at h'
  have h'' := h' q hq
  rw [nat_beq_eq, beq_iff_eq, hc] at h''
  cases ha : anyN 7 (fun k => andB (Nat.beq (pairP k) p) (Nat.beq (pairQ k) q))
  · rw [ha] at h''; exact absurd h'' (by decide)
  · rw [anyN_iff] at ha
    obtain ⟨k, hk, hk'⟩ := ha
    rw [andB_eq, Bool.and_eq_true, nat_beq_eq, nat_beq_eq, beq_iff_eq, beq_iff_eq] at hk'
    exact ⟨k, hk, hk'⟩

end CFSG.KC.GMS.Snd

end
