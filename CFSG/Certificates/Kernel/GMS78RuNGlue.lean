module

public import Certificates.Data.Kernel.GMS78RuN
public import CFSG.Certificates.Kernel.GMS78RuGen

public section

namespace CFSG.KC.GMS.NG

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS CFSG.GMS78Ru CFSG.GMS78RuSim

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by cases c <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl
theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem fget_eq (X i w : Nat) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (pw2 w - 1) = _
  rw [pw2_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem fget_lt (X i w : Nat) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem fget_shift (X a j w : Nat) : fget (X >>> (a * w)) j w = fget X (a + j) w := by
  rw [fget_eq, fget_eq, ← Nat.shiftRight_add, Nat.add_mul]

theorem getD_of_lt {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  have h1 : (X >>> i) &&& 1 = X / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (n : Nat) (f : Nat → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl (h' ▸ h)

theorem allN_of {n : Nat} {f : Nat → Bool} (h : allN n f = true) {i : Nat} (hi : i < n) :
    f i = true := (allN_iff n f).1 h i hi

theorem enum_allN8 {f : Nat → Bool} (h : CFSG.KC.Enum.allN 8 f = true) {d : Nat} (hd : d < 8) :
    f d = true := by
  have e : CFSG.KC.Enum.allN 8 f = andB (allN 8 fun l => f (0 + l)) true := rfl
  rw [e, andB_eq, Bool.and_true] at h
  have := allN_of h hd
  rwa [Nat.zero_add] at this

theorem xorN_succ (n : Nat) (f : Nat → Nat) : xorN (n + 1) f = f n ^^^ xorN n f := rfl

theorem xorN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) : xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem xorN_xor (n : Nat) (f g : Nat → Nat) :
    xorN n (fun i => f i ^^^ g i) = xorN n f ^^^ xorN n g := by
  induction n with
  | zero => exact (Nat.xor_zero 0).symm
  | succ n ih =>
    rw [xorN_succ, xorN_succ, xorN_succ, ih]
    ac_rfl

theorem xorN_lt {n w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

@[expose] noncomputable def selN (n c : Nat) (f : Nat → Nat) : Nat := xorN n fun i => if c.testBit i then f i else 0

theorem selN_succ (n c : Nat) (f : Nat → Nat) :
    selN (n + 1) c f = (if c.testBit n then f n else 0) ^^^ selN n c f := rfl

theorem selN_zero (c : Nat) (f : Nat → Nat) : selN 0 c f = 0 := rfl

theorem ite_xor_bool (a b : Bool) (x : Nat) :
    (if (a ^^ b) = true then x else 0) = (if a = true then x else 0) ^^^ (if b = true then x else 0) := by
  cases a <;> cases b <;> simp

theorem selN_xor_set (n c d : Nat) (f : Nat → Nat) :
    selN n (c ^^^ d) f = selN n c f ^^^ selN n d f := by
  unfold selN
  rw [← xorN_xor]
  congr 1
  funext i
  rw [Nat.testBit_xor, ite_xor_bool]

theorem selN_xor_fun (n c : Nat) (f g : Nat → Nat) :
    selN n c (fun i => f i ^^^ g i) = selN n c f ^^^ selN n c g := by
  unfold selN
  rw [← xorN_xor]
  congr 1
  funext i
  split <;> simp

theorem selN_zero_fun (n c : Nat) : selN n c (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [selN_succ, ih]
    split <;> rfl

theorem selN_zero_set (n : Nat) (f : Nat → Nat) : selN n 0 f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [selN_succ, ih, Nat.zero_testBit]
    simp

theorem selN_congr {n c : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    selN n c f = selN n c g := by
  unfold selN
  exact xorN_congr fun i hi => by rw [h i hi]

theorem selN_congr_set {n c d : Nat} (f : Nat → Nat) (h : ∀ i < n, c.testBit i = d.testBit i) :
    selN n c f = selN n d f := by
  unfold selN
  exact xorN_congr fun i hi => by rw [h i hi]

theorem selN_lt {n c w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) : selN n c f < 2 ^ w := by
  unfold selN
  exact xorN_lt fun i hi => by split; exact h i hi; exact Nat.two_pow_pos w

theorem selN_two_pow {n k : Nat} (f : Nat → Nat) (hk : k < n) : selN n (2 ^ k) f = f k := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    rw [selN_succ, Nat.testBit_two_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · rw [ih h]
      have hne : k ≠ n := Nat.ne_of_lt h
      simp [hne]
    · subst h
      have hz : selN k (2 ^ k) f = 0 := by
        rw [selN_congr_set f (c := 2 ^ k) (d := 0) (fun i hi => by
          rw [Nat.testBit_two_pow, Nat.zero_testBit]
          simp
          omega), selN_zero_set]
      rw [hz]
      simp

theorem xorN_sel (n c : Nat) (f : Nat → Nat) :
    xorN n (fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (bit c i)) = selN n c f := by
  unfold selN
  exact xorN_congr fun i _ => by rw [nIf_eq, bit_eq]

theorem xs8K_eq (c : Nat) (f : Nat → Nat) : xs8K c f = selN 8 c f := xorN_sel 8 c f

theorem maskAppK_eq (A m : Nat) : maskAppK A m = selN 8 m fun k => fget A k 8 :=
  xorN_sel 8 m fun k => fget A k 8

theorem linAppK_eq (R t : Nat) : linAppK R t = selN 3 t fun k => fget R k 3 :=
  xorN_sel 3 t fun k => fget R k 3

theorem sMaskNK_eq (c n : Nat) : sMaskNK c n = selN n c fun i => fget SB i 8 :=
  xorN_sel n c fun i => fget SB i 8

theorem selN_eight (c : Nat) (f : Nat → Nat) : selN 8 c f =
    (if c.testBit 7 then f 7 else 0) ^^^ ((if c.testBit 6 then f 6 else 0) ^^^
    ((if c.testBit 5 then f 5 else 0) ^^^ ((if c.testBit 4 then f 4 else 0) ^^^
    ((if c.testBit 3 then f 3 else 0) ^^^ ((if c.testBit 2 then f 2 else 0) ^^^
    ((if c.testBit 1 then f 1 else 0) ^^^ ((if c.testBit 0 then f 0 else 0) ^^^ 0))))))) := rfl

theorem selN_three (c : Nat) (f : Nat → Nat) : selN 3 c f =
    (if c.testBit 2 then f 2 else 0) ^^^ ((if c.testBit 1 then f 1 else 0) ^^^
    ((if c.testBit 0 then f 0 else 0) ^^^ 0)) := rfl

theorem selN_mod (n c : Nat) (f : Nat → Nat) : selN n (c % 2 ^ n) f = selN n c f :=
  selN_congr_set f fun i hi => by rw [Nat.testBit_mod_two_pow]; simp [hi]

theorem fxor_val (a b : Fin 8) : (a ^^^ b).val = a.val ^^^ b.val := Fin.xor_val_of_two_pow (w := 3) a b

theorem fite_val (p : Prop) [Decidable p] (a : Fin 8) :
    (if p then a else (0 : Fin 8)).val = if p then a.val else 0 := by
  split <;> rfl

theorem xs8_val (c : Nat) (f : Nat → Fin 8) : (CFSG.GMS78RuN.xs8 c f).val = selN 8 c fun i => (f i).val := by
  simp only [CFSG.GMS78RuN.xs8, fxor_val, fite_val, selN_eight, Nat.xor_zero]
  ac_rfl

theorem maskApply_eq (cols : List Nat) (m : Nat) : maskApply cols m = selN 8 m fun k => cols.getD k 0 := by
  simp only [maskApply, sel, selN_eight, Nat.xor_zero]
  ac_rfl

theorem maskApply_eq_maskAppK {cols : List Nat} {A : Nat} (h : ∀ k < 8, cols.getD k 0 = fget A k 8)
    (m : Nat) : maskApply cols m = maskAppK A m := by
  rw [maskApply_eq, maskAppK_eq]
  exact selN_congr h

theorem maskAppK_lt (A m : Nat) : maskAppK A m < 256 := by
  rw [maskAppK_eq]
  exact selN_lt (w := 8) fun k _ => fget_lt A k 8

theorem fget_packV (a b c : Fin 8) :
    fget (packV (a, b, c)) 0 3 = a.val ∧ fget (packV (a, b, c)) 1 3 = b.val ∧
      fget (packV (a, b, c)) 2 3 = c.val := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  change fget (a ||| ((b <<< 3) ||| (c <<< 6))) 0 3 = a ∧ fget (a ||| ((b <<< 3) ||| (c <<< 6))) 1 3 = b ∧
    fget (a ||| ((b <<< 3) ||| (c <<< 6))) 2 3 = c
  revert a ha b hb c hc
  decide +kernel

theorem packV_lt (r : Fin 8 × Fin 8 × Fin 8) : packV r < 512 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := r
  change (a ||| ((b <<< 3) ||| (c <<< 6))) < 512
  revert a ha b hb c hc
  decide +kernel

@[expose] noncomputable def unV (R : Nat) : Lin8 :=
  (⟨fget R 0 3 % 8, Nat.mod_lt _ (by decide)⟩, ⟨fget R 1 3 % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨fget R 2 3 % 8, Nat.mod_lt _ (by decide)⟩)

theorem unV_packV (r : Lin8) : unV (packV r) = r := by
  obtain ⟨a, b, c⟩ := r
  obtain ⟨h0, h1, h2⟩ := fget_packV a b c
  simp only [unV, h0, h1, h2, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt,
    Fin.eta]

theorem packV_unV {R : Nat} (h : R < 512) : packV (unV R) = R := by
  revert h
  revert R
  decide +kernel

theorem packV_inj {r s : Lin8} (h : packV r = packV s) : r = s := by
  rw [← unV_packV r, h, unV_packV]

theorem linApply_val (r : Lin8) (t : Fin 8) : (linApply r t).val = linAppK (packV r) t.val := by
  obtain ⟨a, b, c⟩ := r
  obtain ⟨h0, h1, h2⟩ := fget_packV a b c
  simp only [linAppK_eq, selN_three, h0, h1, h2, linApply, fxor_val, fite_val, Nat.xor_zero]
  ac_rfl

theorem linAppK_lt (R t : Nat) : linAppK R t < 8 := by
  rw [linAppK_eq]
  exact selN_lt (w := 3) fun k _ => fget_lt R k 3

theorem testBit_orN_fields (w : Nat) (f : Nat → Nat) : ∀ n, (∀ i < n, f i < 2 ^ w) →
    ∀ j t, t < w → (orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)).testBit (j * w + t) =
      (decide (j < n) && (f j).testBit t) := by
  intro n
  induction n with
  | zero => intro _ j t _; exact Nat.zero_testBit _
  | succ n ih =>
    intro hf j t ht
    change (Nat.shiftLeft (f n) (w * n) ||| orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)).testBit
      (j * w + t) = _
    rw [Nat.testBit_or, ih (fun i hi => hf i (by omega)) j t ht]
    change ((f n <<< (w * n)).testBit (j * w + t) || _) = _
    rw [Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy j n with h | h | h
    · have h2 : (j + 1) * w ≤ n * w := Nat.mul_le_mul_right w h
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n w] at h2
      have h3 : j < n + 1 := by omega
      have h4 : ¬ (w * n ≤ j * w + t) := by omega
      simp [h, h3, h4]
    · subst h
      simp [Nat.mul_comm w j]
    · have h2 : (n + 1) * w ≤ j * w := Nat.mul_le_mul_right w h
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n w] at h2
      have hz : (f n).testBit (j * w + t - w * n) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf n (by omega))
          (Nat.pow_le_pow_right (by decide) (by omega)))
      have h3 : ¬ j < n := by omega
      have h4 : ¬ j < n + 1 := by omega
      simp [hz, h3, h4]

theorem orN_fields_lt (w n : Nat) (f : Nat → Nat) (hf : ∀ i < n, f i < 2 ^ w) (hw : 0 < w) :
    (orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)) < 2 ^ (n * w) := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  have e := testBit_orN_fields w f n hf (b / w) (b % w) (Nat.mod_lt _ hw)
  rw [Nat.div_add_mod' b w] at e
  have : ¬ b / w < n := by
    intro h
    have h2 : (b / w + 1) * w ≤ n * w := Nat.mul_le_mul_right w h
    have h3 := Nat.div_add_mod' b w
    have h4 := Nat.mod_lt b hw
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  rw [e]
  simp [this]

theorem fget_orN (w n : Nat) (f : Nat → Nat) (hf : ∀ i < n, f i < 2 ^ w) (j : Nat) (hj : j < n) :
    fget (orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)) j w = f j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [fget_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases ht : t < w
  · rw [testBit_orN_fields w f n hf j t ht]
    simp [hj, ht]
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem fget_orN' (w n : Nat) (f : Nat → Nat) (hf : ∀ i < n, f i < 2 ^ w) (j : Nat) (hj : j < n) :
    fget (orN n fun i => Nat.shiftLeft (f i) (Nat.mul i w)) j w = f j := by
  have : (fun i => Nat.shiftLeft (f i) (Nat.mul i w)) = fun i => Nat.shiftLeft (f i) (Nat.mul w i) := by
    funext i
    exact congrArg (Nat.shiftLeft (f i)) (Nat.mul_comm i w)
  rw [this]
  exact fget_orN w n f hf j hj

theorem linCompK_fget (R S k : Nat) (hk : k < 3) : fget (linCompK R S) k 3 = linAppK R (fget S k 3) :=
  fget_orN 3 3 (fun k => linAppK R (fget S k 3)) (fun _ _ => linAppK_lt _ _) k hk

theorem linCompK_lt (R S : Nat) : linCompK R S < 512 :=
  orN_fields_lt 3 3 (fun k => linAppK R (fget S k 3)) (fun _ _ => linAppK_lt _ _) (by decide)

theorem eq_of_fget3 {X Y : Nat} (hX : X < 512) (hY : Y < 512)
    (h : ∀ k < 3, fget X k 3 = fget Y k 3) : X = Y := by
  rw [← packV_unV hX, ← packV_unV hY]
  have : unV X = unV Y := by
    simp only [unV, h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  rw [this]

theorem linComp_pack (r s : Lin8) : linCompK (packV r) (packV s) = packV (linComp r s) := by
  obtain ⟨s0, s1, s2⟩ := s
  change linCompK (packV r) (packV (s0, s1, s2)) = packV (linApply r s0, linApply r s1, linApply r s2)
  obtain ⟨h0, h1, h2⟩ := fget_packV s0 s1 s2
  obtain ⟨g0, g1, g2⟩ := fget_packV (linApply r s0) (linApply r s1) (linApply r s2)
  apply eq_of_fget3 (linCompK_lt _ _) (packV_lt _)
  intro k hk
  rw [linCompK_fget _ _ k hk]
  have e : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases e with rfl | rfl | rfl
  · rw [h0, g0, linApply_val]
  · rw [h1, g1, linApply_val]
  · rw [h2, g2, linApply_val]

theorem bindList_go {α : Type} (f : α → Nat) (T w n : Nat) : ∀ (L : List α) (k : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
      (fun a _ ih i => andB (Nat.beq (f a) (fget T i w)) (ih (Nat.succ i))) L k = true →
    k + L.length = n ∧ ∀ i (h : i < L.length), f L[i] = fget T (k + i) w := by
  intro L
  induction L with
  | nil => intro k h; exact ⟨Nat.eq_of_beq_eq_true h, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | cons a L ih =>
    intro k h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨e, h3⟩ := ih (Nat.succ k) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ i =>
      rw [List.getElem_cons_succ, h3 i (by simp at hi; omega)]
      congr 1
      omega

theorem bindList_get {α : Type} {f : α → Nat} {L : List α} {T w n : Nat} (h : bindList f L T w n = true) :
    L.length = n ∧ ∀ i (hi : i < L.length), f L[i] = fget T i w := by
  obtain ⟨e, h2⟩ := bindList_go f T w n L 0 h
  exact ⟨by omega, fun i hi => by rw [h2 i hi, Nat.zero_add]⟩

theorem bindList_getD {α : Type} {f : α → Nat} {L : List α} {T w n : Nat} (h : bindList f L T w n = true)
    (d : α) {i : Nat} (hi : i < n) : f (L.getD i d) = fget T i w := by
  obtain ⟨e, h2⟩ := bindList_get h
  rw [getD_of_lt _ _ (by omega)]
  exact h2 i (by omega)

theorem bindFin8_eq (L : List (Fin 8)) (T n : Nat) :
    bindFin8 L T n = bindList (fun a => a.val) L T 3 n := rfl

theorem bindFin8_getD {L : List (Fin 8)} {T n : Nat} (h : bindFin8 L T n = true) {i : Nat} (hi : i < n) :
    (L.getD i 0).val = fget T i 3 :=
  bindList_getD (f := fun a : Fin 8 => a.val) h 0 hi

theorem bindFin8_length {L : List (Fin 8)} {T n : Nat} (h : bindFin8 L T n = true) : L.length = n :=
  (bindList_get (f := fun a : Fin 8 => a.val) h).1

theorem bindRows_go (T n k : Nat) : ∀ (L : List (List (Fin 8))) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i k)
      (fun row _ ih i => andB (bindFin8 row (Nat.shiftRight T (Nat.mul (Nat.mul 3 n) i)) n)
        (ih (Nat.succ i))) L j = true →
    j + L.length = k ∧ ∀ i (h : i < L.length), bindFin8 L[i] (T >>> (3 * n * (j + i))) n = true := by
  intro L
  induction L with
  | nil => intro j h; exact ⟨Nat.eq_of_beq_eq_true h, fun i h => absurd h (Nat.not_lt_zero i)⟩
  | cons a L ih =>
    intro j h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨e, h3⟩ := ih (Nat.succ j) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      rw [List.getElem_cons_succ]
      have := h3 i (by simp at hi; omega)
      have e2 : Nat.succ j + i = j + (i + 1) := by omega
      rwa [e2] at this

theorem bindRows_get {L : List (List (Fin 8))} {T n k : Nat} (h : bindRows L T n k = true) :
    L.length = k ∧ ∀ i < k, ∀ t < n, ((L.getD i []).getD t 0).val = fget T (n * i + t) 3 := by
  obtain ⟨e, h2⟩ := bindRows_go T n k L 0 h
  refine ⟨by omega, fun i hi t ht => ?_⟩
  have hi' : i < L.length := by omega
  rw [getD_of_lt L [] hi']
  have := bindFin8_getD (h2 i hi') ht
  have e3 : 3 * n * i = n * i * 3 := by rw [Nat.mul_comm (n * i) 3, Nat.mul_assoc]
  rw [this, Nat.zero_add, e3, fget_shift]

theorem rowAt_go (T n : Nat) : ∀ (L : List (List (Fin 8))) (i : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
      (fun row _ ih i => bIf(Nat.beq i 0, bindFin8 row T n, ih (Nat.sub i 1))) L i = true →
    ∃ h : i < L.length, bindFin8 L[i] T n = true := by
  intro L
  induction L with
  | nil => intro i h; exact (Bool.false_ne_true h).elim
  | cons a L ih =>
    intro i h
    change Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq i 0) = true at h
    cases i with
    | zero => exact ⟨by simp, h⟩
    | succ i =>
      obtain ⟨hi, h'⟩ := ih i h
      exact ⟨by simp; omega, by rw [List.getElem_cons_succ]; exact h'⟩

theorem rowAt_getD {L : List (List (Fin 8))} {i T n : Nat} (h : rowAt L i T n = true) {t : Nat}
    (ht : t < n) : ((L.getD i []).getD t 0).val = fget T t 3 := by
  obtain ⟨hi, h'⟩ := rowAt_go T n L i h
  rw [getD_of_lt _ _ hi]
  exact bindFin8_getD h' ht

theorem gl_closed : allN 512 (fun R => orB (notB (glK R)) (andB (glList.contains (unV R))
    (andB (Nat.beq (linCompK R (packV (linInv (unV R)))) LINID)
    (andB (allN 8 fun k => Nat.beq ((adMat (unV R)).getD k 0) (fget (adK R (packV (linInv (unV R)))) k 8))
      (Nat.beq (glList.idxOf (unV R)) (glIdxK R)))))) = true := by
  decide +kernel

theorem gl_inj : allN 512 (fun R => orB (notB (glK R)) (allN 8 fun a => allN 8 fun b =>
    orB (notB (Nat.beq (linAppK R a) (linAppK R b))) (Nat.beq a b))) = true := by
  decide +kernel

theorem glK_facts (R : Nat) (h : glK R = true) (hR : R < 512) :
    unV R ∈ glList ∧ linCompK R (packV (linInv (unV R))) = LINID ∧
      (∀ k < 8, (adMat (unV R)).getD k 0 = fget (adK R (packV (linInv (unV R)))) k 8) ∧
      glList.idxOf (unV R) = glIdxK R := by
  have := allN_of gl_closed hR
  rw [h, notB_eq, orB_eq, Bool.not_true, Bool.false_or] at this
  obtain ⟨h1, h2⟩ := andB_true this
  obtain ⟨h2, h3⟩ := andB_true h2
  obtain ⟨h3, h4⟩ := andB_true h3
  exact ⟨List.contains_iff_mem.1 h1, Nat.eq_of_beq_eq_true h2,
    fun k hk => Nat.eq_of_beq_eq_true (allN_of h3 hk), Nat.eq_of_beq_eq_true h4⟩

theorem linAppK_inj {R : Nat} (h : glK R = true) (hR : R < 512) {a b : Nat} (ha : a < 8) (hb : b < 8)
    (e : linAppK R a = linAppK R b) : a = b := by
  have := allN_of gl_inj hR
  rw [h, notB_eq, orB_eq, Bool.not_true, Bool.false_or] at this
  have := allN_of (allN_of this ha) hb
  rw [e, Nat.beq_refl, notB_eq, orB_eq, Bool.not_true, Bool.false_or] at this
  exact Nat.eq_of_beq_eq_true this

theorem inv_eq {R I : Nat} (h : glK R = true) (hR : R < 512) (hI : I < 512) (e : linCompK R I = LINID) :
    I = packV (linInv (unV R)) := by
  obtain ⟨-, e2, -, -⟩ := glK_facts R h hR
  apply eq_of_fget3 hI (packV_lt _)
  intro k hk
  apply linAppK_inj h hR (fget_lt I k 3) (fget_lt _ k 3)
  rw [← linCompK_fget R I k hk, ← linCompK_fget R _ k hk, e, e2]

theorem invTab_eq {INV R : Nat} (hI : invTabOK INV = true) (h : glK R = true) (hR : R < 512) :
    fget INV R 9 = packV (linInv (unV R)) := by
  have := allN_of hI hR
  rw [h, notB_eq, orB_eq, Bool.not_true, Bool.false_or] at this
  obtain ⟨-, h2⟩ := andB_true this
  exact inv_eq h hR (fget_lt INV R 9) (Nat.eq_of_beq_eq_true h2)

theorem nAd_eq {INV R : Nat} (hI : invTabOK INV = true) (h : glK R = true) (hR : R < 512) (m : Nat) :
    CFSG.GMS78RuN.nAd (unV R) m = maskAppK (adK R (fget INV R 9)) m := by
  obtain ⟨-, -, hA, -⟩ := glK_facts R h hR
  rw [invTab_eq hI h hR]
  exact maskApply_eq_maskAppK hA m

theorem bindNC_facts {sb : List Nat} {nbt : List (List (Fin 8))} {nc nb : List Nat}
    {dct : List (Fin 8 × Fin 8 × Fin 8)} {ntw : List (List (Fin 8))}
    (h : bindNC sb nbt nc nb dct ntw = true) :
    (∀ i < 8, sb.getD i 0 = fget SB i 8) ∧
    (∀ j < 8, ∀ i < 8, (Gen.nBT nbt j i).val = fget NBT (8 * j + i) 3) ∧
    (∀ k < 8, nc.getD k 0 = fget NCOLS k 8) ∧
    (∀ k < 8, nb.getD k 0 = fget NBAS k 8) ∧
    (∀ d < 8, packV (dct.getD d linId) = fget DC d 9) ∧
    (∀ d < 8, rowAt ntw (glIdxK (fget DC d 9)) (TWD >>> (24 * d)) 8 = true) := by
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h6⟩ := andB_true h
  exact ⟨fun i hi => bindList_getD (f := fun n => n) h1 0 hi,
    fun j hj i hi => (bindRows_get h2).2 j hj i hi,
    fun k hk => bindList_getD (f := fun n => n) h3 0 hk,
    fun k hk => bindList_getD (f := fun n => n) h4 0 hk,
    fun d hd => bindList_getD (f := packV) h5 linId hd, fun d hd => allN_of h6 hd⟩

theorem sMaskN_eq (sb : List Nat) (c n : Nat) : Gen.sMaskN sb c n = selN n c fun i => sb.getD i 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Gen.sMaskN, ih, selN_succ, Nat.xor_comm]

theorem sMaskNK_lt (c n : Nat) : sMaskNK c n < 256 := by
  rw [sMaskNK_eq]
  exact selN_lt (w := 8) fun i _ => fget_lt SB i 8

theorem sMaskN_K {sb : List Nat} (hSB : ∀ i < 8, sb.getD i 0 = fget SB i 8) (c : Nat) {n : Nat}
    (hn : n ≤ 8) : Gen.sMaskN sb c n = sMaskNK c n := by
  rw [sMaskN_eq, sMaskNK_eq]
  exact selN_congr fun i hi => hSB i (by omega)

theorem bC_val {qt : List (Fin 8)} {QT : Nat} (hQ : bindQ qt QT = true) {m n : Nat} (hm : m < 256)
    (hn : n < 256) : (Gen.bC qt m n).val = bCK QT m n := by
  have hmn : m ^^^ n < 256 := Nat.xor_lt_two_pow (n := 8) hm hn
  simp only [Gen.bC, Gen.qC, fxor_val, bindFin8_getD hQ hm, bindFin8_getD hQ hn, bindFin8_getD hQ hmn]
  rfl

theorem gamN_val {qt : List (Fin 8)} {QT : Nat} (hQ : bindQ qt QT = true) {sb : List Nat}
    (hSB : ∀ i < 8, sb.getD i 0 = fget SB i 8) (c c' : Nat) :
    ∀ n ≤ 8, (Gen.gamN qt sb c c' n).val = selN n c fun i => bCK QT (fget SB i 8) (sMaskNK c' i) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [Gen.gamN, fxor_val, ih (by omega), selN_succ, fite_val, hSB n (by omega),
      sMaskN_K hSB c' (Nat.le_of_lt hn), bC_val hQ (fget_lt SB n 8) (sMaskNK_lt c' n), Nat.xor_comm]

theorem gam_val {qt : List (Fin 8)} {QT : Nat} (hQ : bindQ qt QT = true) {sb : List Nat}
    (hSB : ∀ i < 8, sb.getD i 0 = fget SB i 8) (c c' : Nat) :
    (Gen.gam qt sb c c').val = gamK QT c c' := by
  rw [Gen.gam, gamN_val hQ hSB c c' 8 (Nat.le_refl 8)]
  exact (xorN_sel 8 c _).symm

theorem lor_shl_eq {x : Nat} (y : Nat) (hx : x < 256) : x ||| (y <<< 8) = y * 256 + x := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hx, Nat.shiftLeft_eq]

theorem land_255 (y : Nat) {x : Nat} (hx : x < 256) : Nat.land (y * 256 + x) 255 = x := by
  change (y * 256 + x) &&& (2 ^ 8 - 1) = x
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr_8 (y : Nat) {x : Nat} (hx : x < 256) : Nat.shiftRight (y * 256 + x) 8 = y := by
  change (y * 256 + x) >>> 8 = y
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem dMul_closed : ∀ d < 8, ∀ n < 8,
    dMulK d n = (CFSG.GMS78RuS.dMul (CFSG.GMS78RuS.fin8Of d) (CFSG.GMS78RuS.fin8Of n)).val := by
  decide +kernel

theorem foldUp_succ (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp (n + 1) f s = strictN (foldUp n f s) (f n) := rfl

theorem fin8Of_val (d : Fin 8) : CFSG.GMS78RuS.fin8Of d.val = d :=
  Fin.ext (Nat.mod_eq_of_lt d.isLt)

theorem dPartK_go {qt : List (Fin 8)} {QT : Nat} (hQ : bindQ qt QT = true) {sb : List Nat}
    (hSB : ∀ i < 8, sb.getD i 0 = fget SB i 8) (d : Fin 8) (c : Nat) : ∀ n ≤ 8,
    foldUp n (fun n s => Bool.rec (motive := fun _ => Nat) s
      ((fun a t b => Nat.lor (Nat.xor a b) (Nat.shiftLeft (Nat.xor t (gamK QT a b)) 8))
        (Nat.land s 255) (Nat.shiftRight s 8) (pw2 (dMulK d.val n))) (bit c n)) 0 =
      (Gen.dPartN qt sb d c n).2.val * 256 + (Gen.dPartN qt sb d c n).1 ∧
      (Gen.dPartN qt sb d c n).1 < 256 := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨by simp [foldUp, Gen.dPartN], by simp [Gen.dPartN]⟩
  | succ n ih =>
    intro hn
    obtain ⟨e, hlt⟩ := ih (by omega)
    rw [foldUp_succ, strictN_eq, e]
    generalize hp : Gen.dPartN qt sb d c n = p at hlt
    obtain ⟨x, δ⟩ := p
    have hand := land_255 δ.val hlt
    have hshr := shr_8 δ.val hlt
    have hb : pw2 (dMulK d.val n) = 2 ^ (CFSG.GMS78RuS.dMul d (CFSG.GMS78RuS.fin8Of n)).val := by
      rw [pw2_eq, dMul_closed d.val d.isLt n (by omega), fin8Of_val]
    have hblt : 2 ^ (CFSG.GMS78RuS.dMul d (CFSG.GMS78RuS.fin8Of n)).val < 256 :=
      Nat.pow_lt_pow_right (by decide) (CFSG.GMS78RuS.dMul d (CFSG.GMS78RuS.fin8Of n)).isLt
    simp only [Gen.dPartN, hp]
    rw [hand, hshr, hb, bit_eq]
    cases hc : c.testBit n
    · exact ⟨rfl, hlt⟩
    · have hx : x ^^^ 2 ^ (CFSG.GMS78RuS.dMul d (CFSG.GMS78RuS.fin8Of n)).val < 256 :=
        Nat.xor_lt_two_pow (n := 8) hlt hblt
      refine ⟨?_, hx⟩
      simp only [ite_true]
      rw [fxor_val, gam_val hQ hSB]
      exact lor_shl_eq _ hx

theorem dPartK_eq {qt : List (Fin 8)} {QT : Nat} (hQ : bindQ qt QT = true) {sb : List Nat}
    (hSB : ∀ i < 8, sb.getD i 0 = fget SB i 8) (d : Fin 8) (c : Nat) :
    dPartK QT d.val c = (Gen.dPart qt sb d c).2.val * 256 + (Gen.dPart qt sb d c).1 ∧
      (Gen.dPart qt sb d c).1 < 256 :=
  dPartK_go hQ hSB d c 8 (Nat.le_refl 8)

theorem nBetaK_eq (m n : Nat) :
    nBetaK m n = selN 8 (maskAppK NCOLS m) fun j => selN 8 (maskAppK NCOLS n) fun i =>
      fget NBT (8 * j + i) 3 := by
  change (xs8K (maskAppK NCOLS m) fun j => xs8K (maskAppK NCOLS n) fun i => fget NBT (8 * j + i) 3) = _
  rw [xs8K_eq]
  exact selN_congr fun j _ => xs8K_eq _ _

theorem nBetaK_lt (m n : Nat) : nBetaK m n < 8 := by
  rw [nBetaK_eq]
  exact selN_lt (w := 3) fun _ _ => selN_lt (w := 3) fun _ _ => fget_lt _ _ 3

theorem nBeta_val {nbt : List (List (Fin 8))} {nc : List Nat}
    (hNBT : ∀ j < 8, ∀ i < 8, (Gen.nBT nbt j i).val = fget NBT (8 * j + i) 3)
    (hNC : ∀ k < 8, nc.getD k 0 = fget NCOLS k 8) (m n : Nat) :
    (Gen.nBeta nbt nc m n).val = nBetaK m n := by
  simp only [Gen.nBeta, Gen.nCo, xs8_val]
  rw [maskApply_eq_maskAppK hNC, maskApply_eq_maskAppK hNC, nBetaK_eq]
  exact selN_congr fun j hj => selN_congr fun i hi => hNBT j hj i hi

theorem gamTab_fget (R A : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    fget (gamTab R A) (8 * i + j) 3 = if i < j then
      nBetaK (maskAppK A (fget NBAS i 8)) (maskAppK A (fget NBAS j 8)) ^^^
        linAppK R (nBetaK (fget NBAS i 8) (fget NBAS j 8)) else 0 := by
  let F : Nat → Nat := fun ij => Bool.rec (motive := fun _ => Nat) 0
    (Nat.xor (nBetaK (maskAppK A (fget NBAS (ij / 8) 8)) (maskAppK A (fget NBAS (ij % 8) 8)))
      (linAppK R (nBetaK (fget NBAS (ij / 8) 8) (fget NBAS (ij % 8) 8)))) (Nat.blt (ij / 8) (ij % 8))
  have e : gamTab R A = orN 64 fun ij => Nat.shiftLeft (F ij) (Nat.mul 3 ij) := rfl
  have hF : ∀ ij < 64, F ij < 2 ^ 3 := by
    intro ij _
    simp only [F]
    rw [nIf_eq]
    split
    · exact Nat.xor_lt_two_pow (n := 3) (nBetaK_lt _ _) (linAppK_lt _ _)
    · decide
  rw [e, fget_orN 3 64 F hF (8 * i + j) (by omega)]
  have h1 : (8 * i + j) / 8 = i := by omega
  have h2 : (8 * i + j) % 8 = j := by omega
  simp only [F, h1, h2, nIf_eq, Nat.blt_eq]
  rfl

end CFSG.KC.GMS.NG

end
