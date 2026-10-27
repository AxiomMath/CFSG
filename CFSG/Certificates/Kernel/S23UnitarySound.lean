module

public import Certificates.Data.Kernel.S23Unitary
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23UnitaryInputs

public section

namespace CFSG.KC.S23U

open CFSG.KLie.CT CFSG.KC.F4M CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.TwoA.Unitary CFSG.Fischer

@[expose] def wordRowsG (gens : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idRows
  | k :: w => rowsMul gens[k]! (wordRowsG gens w)

@[expose] def b6MatG (b6 : Array (Array ℕ)) (k : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => vec6 (b6[k]!)[(i : ℕ)]!

@[expose] def nuMatG (b6 : Array (Array ℕ)) : Matrix (Fin 6) (Fin 6) F4 :=
  b6MatG b6 0 * b6MatG b6 3 * b6MatG b6 4 * b6MatG b6 7 * b6MatG b6 16

@[expose] def nuPowMG (np : Array (Array ℕ)) (i : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun r => vec6 ((np[i]!)[(r : ℕ)]!)

@[expose] def cycMatG (np : Array (Array ℕ)) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => nuPowMG np i 0

open CFSG.KC.Loop (strictN)
open CFSG.KC.S23 (strictB)

set_option exponentiation.threshold 7000

private theorem xorN_succ (n : ℕ) (f : ℕ → ℕ) : xorN (n + 1) f = f n ^^^ xorN n f := rfl

private theorem xorN_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n),
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

private theorem xorN_lt {n w : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

private theorem andB_iff {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

private theorem notB_iff {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

private theorem orB_iff {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

private theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem brec_eq (b : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t b = if b then t else e := by cases b <;> rfl

private theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by simp only [Nat.beq_eq, decide_eq_true_eq])

private theorem allN_iff {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    change CFSG.KLie.CT.andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

private theorem recAnd_iff (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun l ih => CFSG.KLie.CT.andB (g l) ih) n = true ↔
      ∀ l < n, g l = true := fun n => allN_iff (f := g) (m := n)

private theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool}
    (h : CFSG.KC.Loop.allBelow m hi f = true) (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := (recAnd_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      CFSG.KLie.CT.andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) hi).1 h (i / 64) (by omega)
  have h2 := (recAnd_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  dsimp only at h2
  have hb : Nat.blt i m = true := by rw [Nat.blt_eq]; exact him
  rw [e, hb] at h2
  exact h2

private theorem fget_eq (X i w : ℕ) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

private theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

private theorem fget_zero (i w : ℕ) : fget 0 i w = 0 := by
  rw [fget_eq, Nat.zero_shiftRight, Nat.zero_mod]

private theorem fget_xor (a b i w : ℕ) : fget (a ^^^ b) i w = fget a i w ^^^ fget b i w := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [fget_eq, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  cases decide (k < w) <;> simp [Nat.testBit_xor]

private def Fld (w X : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ i k, k < w → X.testBit (w * i + k) = (g i).testBit k

private theorem fld_congr {w X : ℕ} {g g' : ℕ → ℕ} (h : Fld w X g) (e : ∀ i, g i = g' i) :
    Fld w X g' := fun i k hk => by rw [h i k hk, e]

private theorem fld_or {w A B : ℕ} {g h : ℕ → ℕ} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ||| B) (fun i => g i ||| h i) := by
  intro i k hk
  rw [Nat.testBit_or, hA i k hk, hB i k hk, Nat.testBit_or]

private theorem fld_one {w v : ℕ} (hv : v < 2 ^ w) : Fld w v (fun i => if i = 0 then v else 0) := by
  intro i k hk
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h1 : w ≤ w * i + k := Nat.le_trans (Nat.le_mul_of_pos_right w hi) (Nat.le_add_right _ _)
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) h1))

private theorem fld_shl {w B : ℕ} {h : ℕ → ℕ} (s : ℕ) (hB : Fld w B h) :
    Fld w (B <<< (w * s)) (fun i => if s ≤ i then h (i - s) else 0) := by
  intro i k hk
  rw [Nat.testBit_shiftLeft]
  by_cases hs : s ≤ i
  · have m1 := Nat.mul_le_mul_left w hs
    have e2 : w * i + k - w * s = w * (i - s) + k := by
      rw [Nat.mul_sub]
      omega
    have e1 : w * s ≤ w * i + k := by omega
    simp only [hs, ↓reduceIte, e2, hB _ _ hk, ge_iff_le, e1, decide_true, Bool.true_and]
  · have m1 := Nat.mul_le_mul_left w (by omega : i + 1 ≤ s)
    rw [Nat.mul_add, Nat.mul_one] at m1
    have e1 : ¬ w * s ≤ w * i + k := by omega
    simp only [hs, ↓reduceIte, ge_iff_le, e1, decide_false, Bool.false_and, Nat.zero_testBit]

private theorem fld_term {w F : ℕ} (hF : F < 2 ^ w) (s : ℕ) :
    Fld w (F <<< (w * s)) (fun i => if i = s then F else 0) := by
  refine fld_congr (fld_shl s (fld_one hF)) fun i => ?_
  by_cases h : i = s
  · subst h
    simp
  · by_cases h2 : s ≤ i
    · have : i - s ≠ 0 := by omega
      simp [h, h2, this]
    · simp [h, h2]

private theorem fld_orN {w n : ℕ} {T : ℕ → ℕ} {G : ℕ → ℕ → ℕ} (h : ∀ j < n, Fld w (T j) (G j)) :
    Fld w (orN n T) (fun i => orN n (fun j => G j i)) := by
  induction n with
  | zero =>
    intro i k _
    change Nat.testBit 0 _ = Nat.testBit 0 _
    rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ n ih =>
    exact fld_or (h n (Nat.lt_succ_self n)) (ih fun j hj => h j (Nat.lt_succ_of_lt hj))

private theorem fget_of_fld {w X i : ℕ} {g : ℕ → ℕ} (hX : Fld w X g) (hg : g i < 2 ^ w) :
    fget X i w = g i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [fget_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hk : k < w
  · rw [Nat.mul_comm, hX i k hk]
    simp [hk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

private theorem orN_ite (F : ℕ → ℕ) (o i : ℕ) : ∀ n,
    orN n (fun j => if i = j + o then F j else 0) = if o ≤ i ∧ i < n + o then F (i - o) else 0
  | 0 => by
    have : ¬ (o ≤ i ∧ i < 0 + o) := by omega
    rw [ite_eq_right this]
    rfl
  | n + 1 => by
    change (if i = n + o then F n else 0) ||| orN n (fun j => if i = j + o then F j else 0) = _
    rw [orN_ite F o i n]
    by_cases h : i = n + o
    · have h1 : ¬ (o ≤ i ∧ i < n + o) := by omega
      have h2 : o ≤ i ∧ i < n + 1 + o := by omega
      have h3 : i - o = n := by omega
      rw [ite_eq_left h, ite_eq_right h1, ite_eq_left h2, h3, Nat.or_zero]
    · rw [ite_eq_right h, Nat.zero_or]
      by_cases h1 : o ≤ i ∧ i < n + o
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

private theorem fget_pack {w n : ℕ} {F : ℕ → ℕ} (hF : ∀ j < n, F j < 2 ^ w) {i : ℕ} (hi : i < n) :
    fget (orN n fun j => F j <<< (w * j)) i w = F i := by
  have h := fld_orN (w := w) (n := n) (G := fun j i => if i = j then F j else 0)
    (fun j hj => fld_term (hF j hj) j)
  have e := orN_ite F 0 i n
  simp only [Nat.add_zero, Nat.sub_zero, Nat.zero_le, true_and] at e
  rw [fget_of_fld h, e, ite_eq_left hi]
  rw [e, ite_eq_left hi]
  exact hF i hi

private theorem shl_lt {F w s b : ℕ} (hF : F < 2 ^ w) (hb : s + w ≤ b) : F <<< s < 2 ^ b := by
  rw [Nat.shiftLeft_eq]
  calc F * 2 ^ s < 2 ^ w * 2 ^ s := Nat.mul_lt_mul_of_pos_right hF (Nat.two_pow_pos s)
    _ = 2 ^ (s + w) := by rw [← Nat.pow_add, Nat.add_comm]
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb

private theorem orN_lt {n b : ℕ} {T : ℕ → ℕ} (h : ∀ j < n, T j < 2 ^ b) : orN n T < 2 ^ b := by
  induction n with
  | zero => exact Nat.two_pow_pos b
  | succ n ih =>
    exact Nat.or_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun j hj => h j (Nat.lt_succ_of_lt hj))

private theorem pack_lt {w n b : ℕ} {F : ℕ → ℕ} (hF : ∀ j < n, F j < 2 ^ w) (hb : w * n ≤ b) :
    (orN n fun j => F j <<< (w * j)) < 2 ^ b :=
  orN_lt fun j hj => shl_lt (hF j hj) (by
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ] at this
    omega)

private theorem chain2_spec (p q : ℕ → ℕ → Bool) (n : ℕ) : ∀ (L : List ℕ) (k : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun k => Nat.beq k n)
      (fun x _ ih k => CFSG.KLie.CT.andB (p x k) (CFSG.KLie.CT.andB (q x k) (ih (Nat.succ k)))) L k = true →
    k + L.length = n ∧ ∀ i (hi : i < L.length), p L[i] (k + i) = true ∧ q L[i] (k + i) = true
  | [], k, h => by
    have : k = n := Nat.eq_of_beq_eq_true h
    exact ⟨by simp [this], fun i hi => absurd hi (by simp)⟩
  | x :: L, k, h => by
    change CFSG.KLie.CT.andB (p x k) (CFSG.KLie.CT.andB (q x k) _) = true at h
    rw [andB_iff, andB_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨e, hL⟩ := chain2_spec p q n L (k + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i =>
      have := hL i (by simp at hi; omega)
      rw [Nat.add_right_comm, Nat.add_assoc] at this
      simpa [Nat.add_comm 1 i] using this

private theorem bindW_spec (P w n cnt : ℕ) : ∀ (L : List (Array ℕ)) (k : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun k => Nat.beq k cnt)
      (fun r _ ih k => CFSG.KLie.CT.andB (bindRowW (fget P k (Nat.mul w n)) w n r.toList) (ih (Nat.succ k))) L k
        = true →
    k + L.length = cnt ∧ ∀ i (hi : i < L.length),
      bindRowW (fget P (k + i) (Nat.mul w n)) w n L[i].toList = true
  | [], k, h => by
    have : k = cnt := Nat.eq_of_beq_eq_true h
    exact ⟨by simp [this], fun i hi => absurd hi (by simp)⟩
  | x :: L, k, h => by
    change CFSG.KLie.CT.andB (bindRowW (fget P k (Nat.mul w n)) w n x.toList) _ = true at h
    rw [andB_iff] at h
    obtain ⟨h1, h3⟩ := h
    obtain ⟨e, hL⟩ := bindW_spec P w n cnt L (k + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      have := hL i (by simp at hi; omega)
      rw [Nat.add_right_comm, Nat.add_assoc] at this
      simpa [Nat.add_comm 1 i] using this

private theorem bindW_size {P w n cnt : ℕ} {A : Array (Array ℕ)} (h : bindW P w n cnt A = true) :
    A.size = cnt := by
  obtain ⟨e, -⟩ := bindW_spec P w n cnt A.toList 0 h
  simpa using e

private theorem bindW_ent {P w n cnt : ℕ} {A : Array (Array ℕ)} (h : bindW P w n cnt A = true)
    {k t : ℕ} (hk : k < cnt) (ht : t < n) :
    (A[k]!)[t]! = fget (fget P k (Nat.mul w n)) t w := by
  obtain ⟨e, hL⟩ := bindW_spec P w n cnt A.toList 0 h
  simp only [Nat.zero_add, Array.length_toList] at e hL
  have hk' : k < A.size := by omega
  have hr := chain2_spec (fun x _ => Nat.blt x (pw2 w))
    (fun x t => Nat.beq x (fget (fget P k (Nat.mul w n)) t w)) n (A[k]'hk').toList 0 (hL k hk')
  simp only [Nat.zero_add, Array.length_toList] at hr
  have ht' : t < (A[k]'hk').size := by omega
  rw [getElem!_pos A k hk', getElem!_pos _ t ht']
  have := (hr.2 t ht').2
  simpa using Nat.eq_of_beq_eq_true this

private theorem bindW_ent_ge {P w n cnt : ℕ} {A : Array (Array ℕ)} (h : bindW P w n cnt A = true)
    {k : ℕ} (hk : cnt ≤ k) (t : ℕ) : (A[k]!)[t]! = 0 := by
  have hk' : ¬ k < A.size := by
    rw [bindW_size h]
    omega
  rw [getElem!_neg A k hk']
  rfl

private def Enc (X : ℕ) (R : Array ℕ) : Prop := ∀ t < 20, row20 X t = R[t]!

private theorem actGoR_eq (rows : Array ℕ) (c : ℕ) : ∀ n,
    actGoR rows c n = xorN n (fun i => if c.testBit i then rows[i]! else 0)
  | 0 => rfl
  | n + 1 => by
    rw [actGoR, actGoR_eq rows c n, xorN_succ, Nat.xor_comm]

private theorem act20_eq (M v : ℕ) :
    act20 M v = xorN 20 (fun i => if v.testBit i then row20 M i else 0) := by
  unfold act20
  refine xorN_congr fun i _ => ?_
  rw [brec_eq, bit_eq]

private theorem act20_lt (M v : ℕ) : act20 M v < 2 ^ 20 := by
  rw [act20_eq]
  exact xorN_lt fun i _ => by
    split
    · exact fget_lt _ _ _
    · exact Nat.two_pow_pos 20

private theorem act20_enc {B : ℕ} {RB : Array ℕ} (hB : Enc B RB) (v : ℕ) :
    act20 B v = actR RB v := by
  rw [act20_eq, actR, actGoR_eq]
  exact xorN_congr fun i hi => by rw [hB i hi]

private theorem getElem!_list_map_range (f : ℕ → ℕ) {t : ℕ} (ht : t < 20) :
    (((List.range 20).map f).toArray)[t]! = f t := by
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

private theorem rowsMul_get (A B : Array ℕ) {t : ℕ} (ht : t < 20) :
    (rowsMul A B)[t]! = actR B A[t]! := getElem!_list_map_range _ ht

private theorem rmul_spec {A B : ℕ} {RA RB : Array ℕ} (hA : Enc A RA) (hB : Enc B RB) :
    Enc (rmul A B) (rowsMul RA RB) ∧ rmul A B < 2 ^ 400 := by
  have e : rmul A B = orN 20 fun t => act20 B (row20 A t) <<< (20 * t) := by
    unfold rmul
    rw [strictN_eq, strictN_eq]
    rfl
  rw [e]
  refine ⟨fun t ht => ?_, pack_lt (fun j _ => act20_lt _ _) (by norm_num)⟩
  rw [rowsMul_get _ _ ht, ← hA t ht, ← act20_enc hB]
  exact fget_pack (fun j _ => act20_lt _ _) ht

private theorem id20_spec : Enc ID20 idRows ∧ ID20 < 2 ^ 400 := by
  have e : ID20 = orN 20 fun t => pw2 t <<< (20 * t) := rfl
  have hp : ∀ j < 20, pw2 j < 2 ^ 20 := fun j hj => by
    change 1 <<< j < 2 ^ 20
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) hj
  rw [e]
  refine ⟨fun t ht => ?_, pack_lt hp (by norm_num)⟩
  change fget _ t 20 = _
  rw [fget_pack hp ht]
  change 1 <<< t = _
  unfold idRows
  rw [getElem!_list_map_range _ ht]

private theorem zero_enc : Enc 0 zeroRows := fun t ht => by
  change fget 0 t 20 = _
  rw [fget_zero]
  unfold zeroRows
  rw [getElem!_list_map_range _ ht]

private theorem xor_enc {A B : ℕ} {RA RB : Array ℕ} (hA : Enc A RA) (hB : Enc B RB) :
    Enc (A ^^^ B) (rowsXor RA RB) := fun t ht => by
  change fget _ t 20 = _
  rw [fget_xor]
  change row20 A t ^^^ row20 B t = _
  rw [hA t ht, hB t ht]
  unfold rowsXor
  rw [getElem!_list_map_range _ ht]

private theorem rowsGeom_size (R : Array ℕ) (n : ℕ) : (rowsGeom R n).size = 20 := by
  cases n <;> simp [rowsGeom, zeroRows, rowsXor]

private theorem wordR_spec {G20 : ℕ} {gens : Array (Array ℕ)}
    (hg : ∀ k, Enc (fget G20 k 400) gens[k]!) (w : List ℕ) :
    Enc (wordR G20 w) (wordRowsG gens w) := by
  induction w with
  | nil => exact id20_spec.1
  | cons k w ih => exact (rmul_spec (hg k) ih).1

private noncomputable def geomStep (M st : ℕ) : ℕ :=
  Nat.lor (Nat.xor (Nat.land st (maskN 400)) (Nat.shiftRight st 400))
    (Nat.shiftLeft (rmul (Nat.shiftRight st 400) M) 400)

private noncomputable def geomIter (M n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (Nat.shiftLeft ID20 400) (fun _ st => geomStep M st) n

private theorem geomZero_eq (G20 : ℕ) (w : List ℕ) :
    geomZero G20 w = Nat.beq (Nat.land (geomIter (wordR G20 w) 11) (maskN 400)) 0 := by
  unfold geomZero
  rw [strictB_eq]
  simp only [strictN_eq]
  rfl

private theorem land_mask (st : ℕ) : Nat.land st (maskN 400) = st % 2 ^ 400 := by
  change st &&& (1 <<< 400 - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

private theorem split_mod {S P : ℕ} (hS : S < 2 ^ 400) : (S ||| P <<< 400) % 2 ^ 400 = S := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < 400
  · have : ¬ (k ≥ 400) := by omega
    simp [hk, this]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

private theorem split_shr {S P : ℕ} (hS : S < 2 ^ 400) : (S ||| P <<< 400) >>> 400 = P := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by omega) (by omega)))]
  simp [Nat.add_comm 400 k]

private theorem geomIter_spec {M : ℕ} {RM : Array ℕ} (hM : Enc M RM) : ∀ n,
    ∃ S P, S < 2 ^ 400 ∧ P < 2 ^ 400 ∧ Enc S (rowsGeom RM n) ∧ Enc P (rowsPow RM n) ∧
      geomIter M n = S ||| P <<< 400
  | 0 => ⟨0, ID20, Nat.two_pow_pos 400, id20_spec.2, zero_enc, id20_spec.1, by
      change Nat.shiftLeft ID20 400 = _
      rw [Nat.zero_or]; rfl⟩
  | n + 1 => by
    obtain ⟨S, P, hS, hP, eS, eP, e⟩ := geomIter_spec hM n
    refine ⟨S ^^^ P, rmul P M, Nat.xor_lt_two_pow hS hP, (rmul_spec eP hM).2, xor_enc eS eP,
      (rmul_spec eP hM).1, ?_⟩
    change geomStep M (geomIter M n) = _
    unfold geomStep
    rw [e, land_mask, split_mod hS]
    change (S ^^^ (S ||| P <<< 400) >>> 400) ||| (rmul ((S ||| P <<< 400) >>> 400) M) <<< 400 = _
    rw [split_shr hS]

private theorem geomZero_spec {G20 : ℕ} {w : List ℕ} {RM : Array ℕ}
    (hM : Enc (wordR G20 w) RM) (h : geomZero G20 w = true) : rowsGeom RM 11 = zeroRows := by
  rw [geomZero_eq] at h
  obtain ⟨S, P, hS, hP, eS, eP, e⟩ := geomIter_spec hM 11
  rw [e, land_mask, split_mod hS] at h
  have h0 : S = 0 := Nat.eq_of_beq_eq_true h
  subst h0
  apply Array.ext
  · rw [rowsGeom_size]
    simp [zeroRows]
  · intro i h1 h2
    have hi : i < 20 := by simpa [rowsGeom_size] using h1
    have := eS i hi
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, ← this]
    change fget 0 i 20 = _
    rw [fget_zero]
    unfold zeroRows
    rw [getElem!_list_map_range _ hi]

private theorem b6MatG_eq {B6 : ℕ} {b6 : Array (Array ℕ)} (hb : bindW B6 12 6 17 b6 = true)
    {k : ℕ} (hk : k < 17) : b6MatG b6 k = decM (fget B6 k 72) := by
  ext i j
  unfold b6MatG decM
  simp only [Matrix.of_apply]
  have := bindW_ent hb hk i.2
  change _ = fget (fget B6 k 72) i 12 at this
  rw [this]

private theorem nuPowMG_eq {NP : ℕ} {np : Array (Array ℕ)} (hn : bindW NP 12 6 6 np = true)
    {i : ℕ} (hi : i < 6) : nuPowMG np i = decM (xp NP i) := by
  ext r j
  unfold nuPowMG decM xp
  simp only [Matrix.of_apply]
  have := bindW_ent hn hi r.2
  change _ = fget (fget NP i 72) r 12 at this
  rw [this]

private theorem powsOK_spec {B6 NP : ℕ} {b6 np : Array (Array ℕ)}
    (hb : bindW B6 12 6 17 b6 = true) (hn : bindW NP 12 6 6 np = true)
    (h : powsOK B6 NP = true) :
    nuPowMG np 0 = 1 ∧ nuPowMG np 1 = nuMatG b6 ∧
    (∀ i < 5, nuPowMG np (i + 1) = nuPowMG np i * nuPowMG np 1) ∧
    nuPowMG np 5 * nuPowMG np 5 * nuPowMG np 1 = 1 ∧
    Matrix.trace (nuPowMG np 1) ≠
      Matrix.trace (CFSG.Monster.B.TwoA.Unitary.barM (nuPowMG np 1)) := by
  unfold powsOK at h
  rw [andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [nuPowMG_eq hn (by norm_num), Nat.eq_of_beq_eq_true h1, decM_ONE]
  · rw [nuPowMG_eq hn (by norm_num), Nat.eq_of_beq_eq_true h2]
    simp only [decM_mmul, nuMatG, b6MatG_eq hb (by norm_num : 0 < 17),
      b6MatG_eq hb (by norm_num : 3 < 17), b6MatG_eq hb (by norm_num : 4 < 17),
      b6MatG_eq hb (by norm_num : 7 < 17), b6MatG_eq hb (by norm_num : 16 < 17)]
  · intro i hi
    have := (allN_iff.1 h3) i hi
    rw [nuPowMG_eq hn (by omega : i + 1 < 6), nuPowMG_eq hn (by omega : i < 6),
      nuPowMG_eq hn (by norm_num : 1 < 6), Nat.eq_of_beq_eq_true this, decM_mmul]
  · rw [nuPowMG_eq hn (by norm_num : 5 < 6), nuPowMG_eq hn (by norm_num : 1 < 6),
      ← decM_mmul, ← decM_mmul, Nat.eq_of_beq_eq_true h4, decM_ONE]
  · rw [notB_iff] at h5
    rw [nuPowMG_eq hn (by norm_num : 1 < 6)]
    have e : CFSG.Monster.B.TwoA.Unitary.barM (decM (xp NP 1)) = decM (CFSG.KC.F4M.barM (xp NP 1)) := by
      rw [decM_barM]
      rfl
    rw [e, (tr_sound _).1, (tr_sound _).1]
    exact cF4_ne (tr_sound _).2 (tr_sound _).2 h5

private theorem cycOK_spec {NP CV : ℕ} {np : Array (Array ℕ)} (hn : bindW NP 12 6 6 np = true)
    (h : cycOK NP CV = true) : decM CV * cycMatG np = 1 := by
  unfold cycOK at h
  have h' := Nat.eq_of_beq_eq_true h
  have e : decM (mk fun i j => ent (xp NP i) (nat_lit 0) j) = cycMatG np := by
    ext i j
    rw [← CFSG.KC.F4M.Aux.cF4_ent, CFSG.KC.F4M.Aux.cF4_ent_mk]
    unfold cycMatG
    simp only [Matrix.of_apply]
    rw [nuPowMG_eq hn i.2]
    exact CFSG.KC.F4M.Aux.cF4_ent (xp NP i) 0 j
  rw [← e, ← decM_mmul, h', decM_ONE]

open CFSG.KC.F4M.Aux (cF4_ent cF4_ent_mk fm_spec ent_lt fm_lt testBit_mod4 testBit_div4pow testBit_fget2)

private theorem decM_zero : decM 0 = 0 := by
  ext i j
  change vec6 (fget 0 i 12) j = 0
  rw [fget_zero]
  unfold vec6
  simp only [Nat.zero_div, Nat.zero_mod]
  rfl

private theorem decM_xorN (f : ℕ → ℕ) : ∀ n, decM (xorN n f) = ∑ k ∈ Finset.range n, decM (f k)
  | 0 => decM_zero
  | n + 1 => by
    rw [xorN_succ]
    change decM (Nat.xor (f n) (xorN n f)) = _
    rw [decM_xor, decM_xorN f n, Finset.sum_range_succ, add_comm]

private theorem mk_lt (f : ℕ → ℕ → ℕ) : mk f < 2 ^ 72 := by
  unfold mk
  exact pack_lt (w := 2) (n := 36) (fun j _ => Nat.and_lt_two_pow _ (by norm_num)) (by norm_num)

private theorem smul_lt (a P : ℕ) : smul a P < 2 ^ 72 := by
  unfold smul
  rw [strictN_eq]
  exact mk_lt _

private theorem decM_smul {a : ℕ} (ha : a < 4) (P : ℕ) : decM (smul a P) = cF4 a • decM P := by
  ext i j
  rw [← cF4_ent]
  unfold smul
  rw [strictN_eq, cF4_ent_mk, fm_spec ha (ent_lt _ _ _), cF4_ent]
  rfl

private theorem decM_xpow (NP : ℕ) : ∀ k, decM (xpow NP k) = (decM (xp NP 1)) ^ k
  | 0 => by
    change decM ONE = _
    rw [decM_ONE, pow_zero]
  | k + 1 => by
    change decM (mmul (xpow NP k) (xp NP 1)) = _
    rw [decM_mmul, decM_xpow NP k, pow_succ]

private theorem fget_basisT (NP : ℕ) (sq : Bool) {b : ℕ} (hb : b < 12) :
    fget (basisT NP sq) b 72 =
      Bool.rec (motive := fun _ => ℕ) (smul (Nat.succ (Nat.land b 1)) (xpow NP (Nat.shiftRight b 1)))
        (smul (sqC (Nat.succ (Nat.land b 1))) (xpow NP (Nat.mul 2 (Nat.shiftRight b 1)))) sq := by
  unfold basisT
  exact fget_pack (w := 72) (n := 12)
    (F := fun b => Bool.rec (motive := fun _ => ℕ)
      (smul (Nat.succ (Nat.land b 1)) (xpow NP (Nat.shiftRight b 1)))
      (smul (sqC (Nat.succ (Nat.land b 1))) (xpow NP (Nat.mul 2 (Nat.shiftRight b 1)))) sq)
    (fun j _ => by cases sq <;> exact smul_lt _ _) hb

private theorem fget_basisT_lt (NP : ℕ) (sq : Bool) (b : ℕ) : fget (basisT NP sq) b 72 < 2 ^ 72 :=
  fget_lt _ _ _

private theorem land1_even (i : ℕ) : Nat.land (2 * i) 1 = 0 := by
  change (2 * i) &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

private theorem land1_odd (i : ℕ) : Nat.land (2 * i + 1) 1 = 1 := by
  change (2 * i + 1) &&& 1 = 1
  rw [Nat.and_one_is_mod]
  omega

private theorem shr1_even (i : ℕ) : Nat.shiftRight (2 * i) 1 = i := by
  change (2 * i) >>> 1 = i
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem shr1_odd (i : ℕ) : Nat.shiftRight (2 * i + 1) 1 = i := by
  change (2 * i + 1) >>> 1 = i
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem decM_basisT_even (NP : ℕ) (sq : Bool) {i : ℕ} (hi : i < 6) :
    decM (fget (basisT NP sq) (2 * i) 72) =
      if sq then cF4 (sqC 1) • (decM (xp NP 1)) ^ (2 * i) else cF4 1 • (decM (xp NP 1)) ^ i := by
  rw [fget_basisT NP sq (by omega), land1_even, shr1_even]
  cases sq
  · rw [decM_smul (by norm_num), decM_xpow]
    rfl
  · exact (decM_smul (fm_lt _ _) _).trans (by rw [decM_xpow]; rfl)

private theorem decM_basisT_odd (NP : ℕ) (sq : Bool) {i : ℕ} (hi : i < 6) :
    decM (fget (basisT NP sq) (2 * i + 1) 72) =
      if sq then cF4 (sqC 2) • (decM (xp NP 1)) ^ (2 * i) else cF4 2 • (decM (xp NP 1)) ^ i := by
  rw [fget_basisT NP sq (by omega), land1_odd, shr1_odd]
  cases sq
  · rw [decM_smul (by norm_num), decM_xpow]
    rfl
  · exact (decM_smul (fm_lt _ _) _).trans (by rw [decM_xpow]; rfl)

private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ n, ∑ b ∈ Finset.range (2 * n), g b = ∑ i ∈ Finset.range n, (g (2 * i) + g (2 * i + 1))
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul g n, Finset.sum_range_succ, add_assoc]

private theorem digit_gen (cn i : ℕ) (Y : Matrix (Fin 6) (Fin 6) F4) (A B : F4) (F : ℕ → F4)
    (hF : ∀ d < 4, (if d % 2 = 1 then A else 0) + (if d / 2 % 2 = 1 then B else 0) = F d) :
    (if cn.testBit (2 * i) then A • Y else 0) + (if cn.testBit (2 * i + 1) then B • Y else 0) =
      F ((cn / 4 ^ i) % 4) • Y := by
  have h0 : cn.testBit (2 * i) = ((cn / 4 ^ i) % 4).testBit 0 := by
    rw [testBit_mod4, testBit_div4pow]
    simp [Nat.add_comm]
  have h1 : cn.testBit (2 * i + 1) = ((cn / 4 ^ i) % 4).testBit 1 := by
    rw [testBit_mod4, testBit_div4pow]
    simp [Nat.add_comm]
  have hF' : ∀ d < 4, (if d.testBit 0 then A else 0) + (if d.testBit 1 then B else 0) = F d := by
    intro d hd
    rw [Nat.testBit_zero, show d.testBit 1 = decide (d / 2 ^ 1 % 2 = 1) from Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_true_eq, pow_one]
    exact hF d hd
  rw [h0, h1, ← hF' _ (Nat.mod_lt _ (by norm_num)), add_smul]
  cases ((cn / 4 ^ i) % 4).testBit 0 <;> cases ((cn / 4 ^ i) % 4).testBit 1 <;> simp

private theorem decM_xsum (NP cn : ℕ) (sq : Bool) :
    decM (xsum (basisT NP sq) cn) =
      ∑ i : Fin 6, if sq then (cF4 ((cn / 4 ^ (i : ℕ)) % 4)) ^ 2 • (decM (xp NP 1)) ^ (2 * (i : ℕ))
        else cF4 ((cn / 4 ^ (i : ℕ)) % 4) • (decM (xp NP 1)) ^ (i : ℕ) := by
  unfold xsum
  rw [decM_xorN]
  have hg : ∀ b, decM (Bool.rec (motive := fun _ => ℕ) 0 (fget (basisT NP sq) b 72) (bit cn b)) =
      if cn.testBit b then decM (fget (basisT NP sq) b 72) else 0 := by
    intro b
    rw [brec_eq, bit_eq]
    split
    · rfl
    · exact decM_zero
  simp only [hg]
  rw [show (12 : ℕ) = 2 * 6 from rfl, sum_range_two_mul, ← Fin.sum_univ_eq_sum_range
    (fun i => (if cn.testBit (2 * i) then decM (fget (basisT NP sq) (2 * i) 72) else 0) +
      (if cn.testBit (2 * i + 1) then decM (fget (basisT NP sq) (2 * i + 1) 72) else 0)) 6]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [decM_basisT_even NP sq i.2, decM_basisT_odd NP sq i.2]
  cases sq
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact digit_gen cn i _ _ _ cF4 (fun d hd => by interval_cases d <;> rfl)
  · simp only [↓reduceIte]
    exact digit_gen cn i _ _ _ (fun d => (cF4 d) ^ 2) (fun d hd => by interval_cases d <;> rfl)

private theorem vec6_surj (v : Fin 6 → F4) : ∃ n < 4096, ∀ i : Fin 6, cF4 ((n / 4 ^ (i : ℕ)) % 4) = v i := by
  have hv : ∀ i, (v i).code.val < 4 := fun i => (v i).code.isLt
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  refine ⟨(v 0).code.val + 4 * ((v 1).code.val + 4 * ((v 2).code.val + 4 * ((v 3).code.val +
    4 * ((v 4).code.val + 4 * (v 5).code.val)))), by omega, fun i => ?_⟩
  have key : ∀ x : F4, ∀ m : ℕ, m % 4 = x.code.val → cF4 m = x := by
    intro x m hm
    unfold cF4
    exact congrArg F4.mk (Fin.ext hm)
  apply key
  fin_cases i <;> simp <;> omega

private theorem sq_sum (X : Matrix (Fin 6) (Fin 6) F4) (c : Fin 6 → F4) :
    (∑ i : Fin 6, c i • X ^ (i : ℕ)) * (∑ i : Fin 6, c i • X ^ (i : ℕ)) =
      ∑ i : Fin 6, (c i) ^ 2 • X ^ (2 * (i : ℕ)) := by
  let φ : Polynomial F4 →ₐ[F4] Matrix (Fin 6) (Fin 6) F4 := Polynomial.aeval X
  have e1 : ∑ i : Fin 6, c i • X ^ (i : ℕ) =
      φ (∑ i : Fin 6, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) := by
    simp [φ, map_sum, Algebra.smul_def]
  have e2 : ∑ i : Fin 6, (c i) ^ 2 • X ^ (2 * (i : ℕ)) =
      φ (∑ i : Fin 6, (Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) ^ 2) := by
    simp only [map_sum, map_pow, map_mul, φ, Polynomial.aeval_C, Polynomial.aeval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_pow, ← pow_mul, mul_comm (i : ℕ) 2]
  rw [e1, e2, ← map_mul, ← sq]
  congr 1
  exact sum_pow_char (p := 2) _ _

private theorem cF4_inj {c d : ℕ} (hc : c < 4) (hd : d < 4) (h : cF4 c = cF4 d) : c = d := by
  have h2 : c % 4 = d % 4 := congrArg (fun x : F4 => x.code.val) h
  rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h2

private theorem testBit_via_fget (X k : ℕ) (hk : k < 72) :
    X.testBit k = (fget X (k / 2) 2).testBit (k % 2) := by
  rw [testBit_fget2, decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

private theorem decM_inj {A B : ℕ} (hA : A < 2 ^ 72) (hB : B < 2 ^ 72) (h : decM A = decM B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 72
  · rw [testBit_via_fget A k hk, testBit_via_fget B k hk]
    suffices hf : fget A (k / 2) 2 = fget B (k / 2) 2 by rw [hf]
    have ht : k / 2 < 36 := by omega
    have h1 : (k / 2) / 6 < 6 := by omega
    have h2 : (k / 2) % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have := congrFun (congrFun h ⟨(k / 2) / 6, h1⟩) ⟨(k / 2) % 6, h2⟩
    rw [← cF4_ent, ← cF4_ent] at this
    have e := cF4_inj (ent_lt _ _ _) (ent_lt _ _ _) this
    have e6 : 6 * ((k / 2) / 6) + (k / 2) % 6 = k / 2 := by omega
    change fget A (6 * ((k / 2) / 6) + (k / 2) % 6) 2 = fget B (6 * ((k / 2) / 6) + (k / 2) % 6) 2 at e
    rwa [e6] at e
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB (Nat.pow_le_pow_right (by omega) (by omega)))]

private theorem decM_mulONE {a : ℕ} (ha : a < 4) :
    decM (Nat.mul a ONE) = cF4 a • (1 : Matrix (Fin 6) (Fin 6) F4) := by
  interval_cases a <;> (ext i j; fin_cases i <;> fin_cases j <;> rfl)

private theorem mulONE_lt {a : ℕ} (ha : a < 4) : Nat.mul a ONE < 2 ^ 72 := by
  interval_cases a <;> (unfold ONE; norm_num)

private theorem defect_eq_zero_of {A : ℕ} (hA : A < 2 ^ 72) (h : IsScalarM (decM A)) :
    defect A = 0 := by
  unfold defect
  have ha : ent A 0 0 < 4 := ent_lt _ _ _
  have e : decM A = decM (Nat.mul (ent A 0 0) ONE) := by
    rw [decM_mulONE ha]
    ext i j
    have hij := h (i, j)
    simp only at hij
    rw [hij]
    have h00 : decM A 0 0 = cF4 (ent A 0 0) := (cF4_ent A 0 0).symm
    rw [h00]
    by_cases hi : i = j
    · simp [hi]
    · simp [hi, Matrix.one_apply_ne hi]
  have e2 : A = Nat.mul (ent A 0 0) ONE := decM_inj hA (mulONE_lt ha) e
  exact (congrArg (fun x => Nat.xor x (Nat.mul (ent A 0 0) ONE)) e2).trans (Nat.xor_self _)

private theorem isScalar_of_defect {A : ℕ} (h : defect A = 0) : IsScalarM (decM A) := by
  unfold defect at h
  have ha : ent A 0 0 < 4 := ent_lt _ _ _
  have e : A = Nat.mul (ent A 0 0) ONE := by
    apply Nat.eq_of_testBit_eq
    intro k
    have := congrArg (fun x => x.testBit k) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    simpa using this
  rw [(congrArg decM e).trans (decM_mulONE ha)]
  intro p
  by_cases hp : p.1 = p.2
  · simp [hp]
  · simp [hp, Matrix.one_apply_ne hp]

private theorem xsum_lt (T c : ℕ) (hT : ∀ b, fget T b 72 < 2 ^ 72) : xsum T c < 2 ^ 72 := by
  unfold xsum
  exact xorN_lt fun b _ => by
    rw [brec_eq]
    split
    · exact hT b
    · exact Nat.two_pow_pos 72

private theorem scalOK_spec {NP : ℕ} {np : Array (Array ℕ)} (hn : bindW NP 12 6 6 np = true)
    (hpow : ∀ i < 6, nuPowMG np i = (nuPowMG np 1) ^ i) (h : scalOK NP = true)
    (c : Fin 6 → F4)
    (hs : IsScalarM ((∑ i : Fin 6, c i • nuPowMG np i) * ∑ i : Fin 6, c i • nuPowMG np i)) :
    IsScalarM (∑ i : Fin 6, c i • nuPowMG np i) := by
  have hX : nuPowMG np 1 = decM (xp NP 1) := nuPowMG_eq hn (by norm_num)
  have hS : ∑ i : Fin 6, c i • nuPowMG np i = ∑ i : Fin 6, c i • (decM (xp NP 1)) ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => by rw [hpow i i.2, hX]
  rw [hS] at hs ⊢
  obtain ⟨cn, hcn, hd⟩ := vec6_surj c
  unfold scalOK at h
  rw [strictB_eq, strictB_eq] at h
  have h2 := allBelow_spec h (by norm_num) cn hcn
  rw [orB_iff, notB_iff] at h2
  have eT : decM (xsum (basisT NP false) cn) = ∑ i : Fin 6, c i • (decM (xp NP 1)) ^ (i : ℕ) := by
    rw [decM_xsum]
    exact Finset.sum_congr rfl fun i _ => by simp [hd i]
  have eTS : decM (xsum (basisT NP true) cn) =
      (∑ i : Fin 6, c i • (decM (xp NP 1)) ^ (i : ℕ)) *
        ∑ i : Fin 6, c i • (decM (xp NP 1)) ^ (i : ℕ) := by
    rw [decM_xsum, sq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [hd i]
  rcases h2 with h2 | h2
  · exfalso
    have h3 : defect (xsum (basisT NP true) cn) = 0 :=
      defect_eq_zero_of (xsum_lt _ _ (fget_basisT_lt _ _)) (by rw [eTS]; exact hs)
    rw [h3] at h2
    exact absurd h2 (by decide)
  · rw [← eT]
    exact isScalar_of_defect (Nat.eq_of_beq_eq_true h2)

theorem sound (gens b6 np : Array (Array ℕ)) (w : List ℕ) (Ci : Matrix (Fin 6) (Fin 6) F4)
    (G20 B6 NP CV : Nat) (hG : G20 < 2 ^ 6800)
    (hb : CFSG.KLie.CT.andB (bindW G20 20 20 17 gens) (CFSG.KLie.CT.andB (bindW B6 12 6 17 b6) (bindW NP 12 6 6 np)) = true)
    (hcv : Ci = decM CV)
    (hk : CFSG.KLie.CT.andB (geomZero G20 w) (CFSG.KLie.CT.andB (powsOK B6 NP) (CFSG.KLie.CT.andB (cycOK NP CV) (scalOK NP))) = true) :
    (rowsGeom (wordRowsG gens w) 11 = zeroRows)
    ∧ (nuPowMG np 0 = 1)
    ∧ (nuPowMG np 1 = nuMatG b6)
    ∧ (∀ i < 5, nuPowMG np (i + 1) = nuPowMG np i * nuPowMG np 1)
    ∧ (nuPowMG np 5 * nuPowMG np 5 * nuPowMG np 1 = 1)
    ∧ (Matrix.trace (nuPowMG np 1) ≠ Matrix.trace (barM (nuPowMG np 1)))
    ∧ (Ci * cycMatG np = 1)
    ∧ (∀ c : Fin 6 → F4,
       IsScalarM ((∑ i : Fin 6, c i • nuPowMG np i) * ∑ i : Fin 6, c i • nuPowMG np i) →
         IsScalarM (∑ i : Fin 6, c i • nuPowMG np i)) := by
  rw [andB_iff, andB_iff] at hb
  obtain ⟨hb1, hb2, hb3⟩ := hb
  rw [andB_iff, andB_iff, andB_iff] at hk
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  have hgens : ∀ k, Enc (fget G20 k 400) gens[k]! := by
    intro k t ht
    by_cases hk17 : k < 17
    · exact (bindW_ent hb1 hk17 ht).symm
    · rw [bindW_ent_ge hb1 (by omega)]
      have hz : fget G20 k 400 = 0 := by
        rw [fget_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt, Nat.zero_mod]
        refine Nat.lt_of_lt_of_le hG (Nat.pow_le_pow_right (by norm_num) ?_)
        omega
      rw [hz]
      change fget 0 t 20 = 0
      exact fget_zero _ _
  obtain ⟨p1, p2, p3, p4, p5⟩ := powsOK_spec hb2 hb3 hk2
  have hpow : ∀ i, i < 6 → nuPowMG np i = (nuPowMG np 1) ^ i := by
    intro i
    induction i with
    | zero => intro _; rw [pow_zero]; exact p1
    | succ i ih => intro hi; rw [p3 i (by omega), ih (by omega), pow_succ]
  exact ⟨geomZero_spec (wordR_spec hgens w) hk1, p1, p2, p3, p4, p5,
    by rw [hcv]; exact cycOK_spec hb3 hk3, fun c hc => scalOK_spec hb3 hpow hk4 c hc⟩

end CFSG.KC.S23U

end
