module

public import Certificates.Data.Kernel.Misc.PermG2U
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Quasithin.Background.G2UCodes
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Misc.G2U

open Matrix CFSG.Quasithin.G2U CFSG.KC.Misc.Clos

@[expose] noncomputable def pk (w : ℕ) (m : List ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun r _ ih => Nat.lor r (Nat.shiftLeft ih w)) m

theorem pk_nil (w : ℕ) : pk w [] = 0 := rfl

theorem pk_cons (w r : ℕ) (t : List ℕ) : pk w (r :: t) = r ||| (pk w t <<< w) := rfl

theorem rows2_eq (m : List ℕ) : rows2 m = pk 14 m := rfl

theorem codes9_eq (m : List ℕ) : codes9 m = pk 4 m := rfl

theorem fldN_eq (x o m : ℕ) : fldN x o m = x / 2 ^ o % 2 ^ m := by
  change (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pk_cons_eq {w r : ℕ} (hr : r < 2 ^ w) (t : List ℕ) :
    pk w (r :: t) = r + 2 ^ w * pk w t := by
  rw [pk_cons, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

theorem pk_lt {w : ℕ} {m : List ℕ} (h : ∀ x ∈ m, x < 2 ^ w) : pk w m < 2 ^ (w * m.length) := by
  induction m with
  | nil => simp [pk_nil]
  | cons r t ih =>
    have hr := h r (List.mem_cons_self ..)
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [pk_cons_eq hr, List.length_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (w * t.length))]
    calc r + 2 ^ w * pk w t < 2 ^ w + 2 ^ w * pk w t := by omega
      _ = 2 ^ w * (pk w t + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * t.length) := Nat.mul_le_mul_left _ ht

theorem fld_pk {w : ℕ} {m : List ℕ} (h : ∀ x ∈ m, x < 2 ^ w) (k : ℕ) :
    pk w m / 2 ^ (w * k) % 2 ^ w = m.getD k 0 := by
  induction m generalizing k with
  | nil => simp [pk_nil]
  | cons r t ih =>
    have hr := h r (List.mem_cons_self ..)
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hp : 0 < 2 ^ w := Nat.two_pow_pos w
    rw [pk_cons_eq hr]
    cases k with
    | zero =>
      rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      rfl
    | succ k =>
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * k)), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add, ht k]
      simp

theorem pk_inj {w : ℕ} {m m' : List ℕ} (h : ∀ x ∈ m, x < 2 ^ w) (h' : ∀ x ∈ m', x < 2 ^ w)
    (hl : m.length = m'.length) (e : pk w m = pk w m') : m = m' := by
  refine List.ext_getElem hl fun i hi hi' => ?_
  have h1 := fld_pk h i
  have h2 := fld_pk h' i
  rw [e, h2, List.getD_eq_getElem _ _ hi'] at h1
  rw [List.getD_eq_getElem _ _ hi] at h1
  exact h1.symm

theorem pk_append (w : ℕ) (l : List ℕ) (x : ℕ) :
    pk w (l ++ [x]) = pk w l ||| (x <<< (w * l.length)) := by
  induction l with
  | nil => simp [pk_cons, pk_nil]
  | cons r l ih =>
    rw [List.cons_append, pk_cons, ih, pk_cons, Nat.shiftLeft_or_distrib, List.length_cons,
      Nat.mul_succ, Nat.add_comm (w * l.length) w, Nat.shiftLeft_add, Nat.or_assoc]
    rw [← Nat.shiftLeft_add, ← Nat.shiftLeft_add, Nat.add_comm]

@[expose] noncomputable def bld (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (f k) (Nat.mul w k))) n

theorem bld_eq (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : bld w f n = pk w ((List.range n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bld w f n ||| (f n <<< (w * n)) = _
    rw [ih, List.range_succ, List.map_append, List.map_singleton, pk_append, List.length_map,
      List.length_range]

theorem m2_eq (x y : ℕ) : m2 x y = bld 14 (row2 x y) 14 := rfl

theorem m9_eq (x y : ℕ) : m9 x y = bld 4 (fun k => ent9 x y (k / 3) (k % 3)) 9 := rfl

theorem testBit_pk {w : ℕ} {m : List ℕ} (h : ∀ x ∈ m, x < 2 ^ w) (i : ℕ) {k : ℕ} (hk : k < w) :
    (pk w m).testBit (w * i + k) = (m.getD i 0).testBit k := by
  rw [← fld_pk h i, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hk]

theorem blt_land (x p : ℕ) : Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 p)) = x.testBit p := by
  change Nat.blt 0 (x &&& (1 <<< p)) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  cases hb : x.testBit p
  · have h0 : x &&& 2 ^ p = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : p = j
      · subst hj
        simp [hb]
      · simp [hj]
    rw [h0]
    rfl
  · have hne : x &&& 2 ^ p ≠ 0 := fun h0 => by
      have := congrArg (fun z => z.testBit p) h0
      simp only [Nat.testBit_and, Nat.testBit_two_pow_self, hb, Nat.zero_testBit] at this
      exact absurd this (by decide)
    exact Nat.blt_eq.mpr (Nat.pos_of_ne_zero hne)

@[expose] noncomputable def xr (b : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (g k)) (b k)) n

theorem xr_congr {b b' : ℕ → Bool} {g g' : ℕ → ℕ} {n : ℕ} (hb : ∀ k < n, b k = b' k)
    (hg : ∀ k < n, g k = g' k) : xr b g n = xr b' g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Nat) (xr b g n) (Nat.xor (xr b g n) (g n)) (b n) =
      Bool.rec (motive := fun _ => Nat) (xr b' g' n) (Nat.xor (xr b' g' n) (g' n)) (b' n)
    rw [ih (fun k hk => hb k (by omega)) (fun k hk => hg k (by omega)), hb n (by omega),
      hg n (by omega)]

theorem foldr_xor (b : ℕ → Bool) (g : ℕ → ℕ) (a : ℕ) (l : List ℕ) :
    l.foldr (fun k acc => if b k then g k ^^^ acc else acc) a =
      l.foldr (fun k acc => if b k then g k ^^^ acc else acc) 0 ^^^ a := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldr_cons, ih]
    split <;> simp [Nat.xor_assoc]

theorem xr_eq (b : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) :
    xr b g n = (List.range n).foldr (fun k acc => if b k then g k ^^^ acc else acc) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Nat) (xr b g n) (Nat.xor (xr b g n) (g n)) (b n) = _
    rw [List.range_succ, List.foldr_append, foldr_xor, ← ih, List.foldr_cons, List.foldr_nil]
    cases b n
    · simp
    · simp only [if_true, Nat.xor_zero]
      rfl

theorem canon2_iff {m : List ℕ} : canon2 m = true ↔ m.length = 14 ∧ ∀ x ∈ m, x < 2 ^ 14 := by
  simp [canon2]

theorem canon3_iff {m : List ℕ} : canon3 m = true ↔ m.length = 9 ∧ ∀ x ∈ m, x < 9 := by
  simp [canon3]

theorem getD_lt {m : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ x ∈ m, x < B) (k : ℕ) :
    m.getD k 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : m[k]? with
  | none => exact hB
  | some x => exact h x (List.mem_of_getElem? hk)

theorem row2_rows2 {m n : List ℕ} (hm : ∀ x ∈ m, x < 2 ^ 14) (hn : ∀ x ∈ n, x < 2 ^ 14)
    (i : ℕ) : row2 (rows2 m) (rows2 n) i = rowMul (m.getD i 0) n := by
  change xr (fun k => Nat.blt 0 (Nat.land (rows2 m) (Nat.shiftLeft 1 (Nat.add (Nat.mul 14 i) k))))
    (fun k => fldN (rows2 n) (Nat.mul 14 k) 14) 14 = _
  rw [rowMul, ← xr_eq]
  refine xr_congr (fun k hk => ?_) (fun k _ => ?_)
  · rw [blt_land]
    exact testBit_pk hm i hk
  · rw [fldN_eq]
    exact fld_pk hn k

theorem rowMul_lt {n : List ℕ} (hn : ∀ x ∈ n, x < 2 ^ 14) (r : ℕ) : rowMul r n < 2 ^ 14 := by
  unfold rowMul
  induction (List.range 14) with
  | nil => exact Nat.two_pow_pos 14
  | cons k l ih =>
    rw [List.foldr_cons]
    split
    · exact Nat.xor_lt_two_pow (getD_lt (Nat.two_pow_pos 14) hn k) ih
    · exact ih

theorem map_range_getD {m : List ℕ} {n : ℕ} (h : m.length = n) :
    (List.range n).map (m.getD · 0) = m := by
  subst h
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]

theorem m2_rows2 {m n : List ℕ} (hm : canon2 m = true) (hn : canon2 n = true) :
    m2 (rows2 m) (rows2 n) = rows2 (mul2 m n) := by
  obtain ⟨hml, hmb⟩ := canon2_iff.1 hm
  obtain ⟨_, hnb⟩ := canon2_iff.1 hn
  rw [m2_eq, bld_eq, rows2_eq, mul2]
  congr 1
  conv_rhs => rw [← map_range_getD hml, List.map_map]
  exact List.map_congr_left fun i _ => row2_rows2 hmb hnb i

theorem canon2_mul2 {m n : List ℕ} (hm : canon2 m = true) (hn : canon2 n = true) :
    canon2 (mul2 m n) = true := by
  obtain ⟨hml, _⟩ := canon2_iff.1 hm
  obtain ⟨_, hnb⟩ := canon2_iff.1 hn
  refine canon2_iff.2 ⟨by rw [mul2, List.length_map, hml], fun x hx => ?_⟩
  obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
  exact rowMul_lt hnb r

theorem e9_codes9 {m : List ℕ} (hm : ∀ x ∈ m, x < 2 ^ 4) (k : ℕ) : e9 (codes9 m) k = m.getD k 0 := by
  rw [e9, fldN_eq, codes9_eq]
  exact fld_pk hm k

theorem ent9_codes9 {m n : List ℕ} (hm : ∀ x ∈ m, x < 2 ^ 4) (hn : ∀ x ∈ n, x < 2 ^ 4)
    (i j : ℕ) : ent9 (codes9 m) (codes9 n) i j = ent3 m n i j := by
  simp only [ent9, e9_codes9 hm, e9_codes9 hn]
  rfl

theorem add9_lt (x y : ℕ) : add9 x y < 9 := by
  unfold add9
  omega

theorem canon3_mul3 (m n : List ℕ) : canon3 (mul3 m n) = true := by
  refine canon3_iff.2 ⟨rfl, fun x hx => ?_⟩
  simp only [mul3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h <;> rw [h] <;> exact add9_lt _ _

theorem m9_codes9 {m n : List ℕ} (hm : canon3 m = true) (hn : canon3 n = true) :
    m9 (codes9 m) (codes9 n) = codes9 (mul3 m n) := by
  have hmb : ∀ x ∈ m, x < 2 ^ 4 := fun x hx => by
    have := (canon3_iff.1 hm).2 x hx
    omega
  have hnb : ∀ x ∈ n, x < 2 ^ 4 := fun x hx => by
    have := (canon3_iff.1 hn).2 x hx
    omega
  rw [m9_eq, bld_eq, codes9_eq (mul3 m n)]
  congr 1
  simp only [ent9_codes9 hmb hnb]
  rfl

@[expose] noncomputable def code2 (v : Fin 14 → ZMod 2) : ℕ :=
  pk 1 (List.ofFn fun j => (v j).val)

@[expose] noncomputable def rowsOf2 (M : Matrix (Fin 14) (Fin 14) (ZMod 2)) : List ℕ :=
  List.ofFn fun i => code2 (M i)

@[expose] noncomputable def encM2 (M : Matrix (Fin 14) (Fin 14) (ZMod 2)) : ℕ :=
  rows2 (rowsOf2 M)

theorem bits_lt (v : Fin 14 → ZMod 2) : ∀ x ∈ List.ofFn (fun j => (v j).val), x < 2 ^ 1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact ZMod.val_lt (v j)

theorem code2_lt (v : Fin 14 → ZMod 2) : code2 v < 2 ^ 14 := by
  have h := pk_lt (bits_lt v)
  rwa [List.length_ofFn] at h

theorem testBit_code2 (v : Fin 14 → ZMod 2) (j : Fin 14) :
    bz ((code2 v).testBit j) = v j := by
  have h := fld_pk (bits_lt v) j
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, Nat.one_mul, Nat.pow_one] at h
  rw [code2, Nat.testBit_eq_decide_div_mod_eq, h]
  generalize v j = z
  revert z
  decide

theorem canon2_rowsOf2 (M : Matrix (Fin 14) (Fin 14) (ZMod 2)) : canon2 (rowsOf2 M) = true := by
  refine canon2_iff.2 ⟨List.length_ofFn, fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact code2_lt _

theorem dec2_rowsOf2 (M : Matrix (Fin 14) (Fin 14) (ZMod 2)) : dec2 (rowsOf2 M) = M := by
  ext i j
  simp only [dec2, Matrix.of_apply, rowsOf2]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact testBit_code2 (M i) j

theorem rowsOf2_dec2 {m : List ℕ} (h : canon2 m = true) : rowsOf2 (dec2 m) = m :=
  dec2_injective (canon2_rowsOf2 _) h (dec2_rowsOf2 _)

theorem rowsOf2_mul (A B : Matrix (Fin 14) (Fin 14) (ZMod 2)) :
    rowsOf2 (A * B) = mul2 (rowsOf2 A) (rowsOf2 B) :=
  dec2_injective (canon2_rowsOf2 _) (canon2_mul2 (canon2_rowsOf2 A) (canon2_rowsOf2 B))
    (by rw [dec2_rowsOf2, dec2_mul2, dec2_rowsOf2, dec2_rowsOf2])

@[expose] noncomputable def encG2 (g : GL (Fin 14) (ZMod 2)) : ℕ := encM2 g

theorem encM2_injective : Function.Injective encM2 := by
  intro A B e
  have hA := canon2_iff.1 (canon2_rowsOf2 A)
  have hB := canon2_iff.1 (canon2_rowsOf2 B)
  have h : rowsOf2 A = rowsOf2 B := pk_inj hA.2 hB.2 (hA.1.trans hB.1.symm) e
  rw [← dec2_rowsOf2 A, h, dec2_rowsOf2]

theorem enc2 : ClosEnc encG2 m2 (encG2 1) where
  enc_one := rfl
  enc_mul a b := by
    rw [encG2, encG2, encG2, Units.val_mul, encM2, encM2, encM2, rowsOf2_mul,
      m2_rows2 (canon2_rowsOf2 _) (canon2_rowsOf2 _)]
  inj _ _ e := Units.ext (encM2_injective e)

theorem encM2_dec2 {m : List ℕ} (h : canon2 m = true) : encM2 (dec2 m) = rows2 m := by
  rw [encM2, rowsOf2_dec2 h]

@[expose] def code9 (z : F9) : ℕ := z.re.val + 3 * z.im.val

@[expose] def ents9 (M : Matrix (Fin 3) (Fin 3) F9) : List ℕ :=
  [code9 (M 0 0), code9 (M 0 1), code9 (M 0 2), code9 (M 1 0), code9 (M 1 1), code9 (M 1 2),
    code9 (M 2 0), code9 (M 2 1), code9 (M 2 2)]

@[expose] noncomputable def encM9 (M : Matrix (Fin 3) (Fin 3) F9) : ℕ :=
  codes9 (ents9 M)

theorem code9_lt (z : F9) : code9 z < 9 := by
  have h1 := ZMod.val_lt z.re
  have h2 := ZMod.val_lt z.im
  unfold code9
  omega

theorem dec9_code9 (z : F9) : dec9 (code9 z) = z := by
  have h1 := ZMod.val_lt z.re
  have h2 := ZMod.val_lt z.im
  have e1 : code9 z % 3 = z.re.val := by
    unfold code9
    omega
  have e2 : code9 z / 3 = z.im.val := by
    unfold code9
    omega
  ext
  · change (((code9 z % 3 : ℕ)) : ZMod 3) = z.re
    rw [e1, ZMod.natCast_zmod_val]
  · change (((code9 z / 3 : ℕ)) : ZMod 3) = z.im
    rw [e2, ZMod.natCast_zmod_val]

theorem canon3_ents9 (M : Matrix (Fin 3) (Fin 3) F9) : canon3 (ents9 M) = true := by
  refine canon3_iff.2 ⟨rfl, fun x hx => ?_⟩
  simp only [ents9, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h <;> rw [h] <;> exact code9_lt _

theorem dec3_ents9 (M : Matrix (Fin 3) (Fin 3) F9) : dec3 (ents9 M) = M := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> exact dec9_code9 _

theorem ents9_dec3 {m : List ℕ} (h : canon3 m = true) : ents9 (dec3 m) = m :=
  dec3_injective (canon3_ents9 _) h (dec3_ents9 _)

theorem ents9_mul (A B : Matrix (Fin 3) (Fin 3) F9) :
    ents9 (A * B) = mul3 (ents9 A) (ents9 B) :=
  dec3_injective (canon3_ents9 _) (canon3_mul3 _ _)
    (by rw [dec3_ents9, dec3_mul3, dec3_ents9, dec3_ents9])

@[expose] noncomputable def encG9 (g : GL (Fin 3) F9) : ℕ := encM9 g

theorem ents9_lt (M : Matrix (Fin 3) (Fin 3) F9) : ∀ x ∈ ents9 M, x < 2 ^ 4 := fun x hx => by
  have := (canon3_iff.1 (canon3_ents9 M)).2 x hx
  omega

theorem encM9_injective : Function.Injective encM9 := by
  intro A B e
  have h : ents9 A = ents9 B := pk_inj (ents9_lt A) (ents9_lt B) rfl e
  rw [← dec3_ents9 A, h, dec3_ents9]

theorem enc9 : ClosEnc encG9 m9 (encG9 1) where
  enc_one := rfl
  enc_mul a b := by
    rw [encG9, encG9, encG9, Units.val_mul, encM9, encM9, encM9, ents9_mul,
      m9_codes9 (canon3_ents9 _) (canon3_ents9 _)]
  inj _ _ e := Units.ext (encM9_injective e)

theorem encG9_lt (g : GL (Fin 3) F9) : encG9 g < 2 ^ 36 := pk_lt (ents9_lt _)

theorem encM9_dec3 {m : List ℕ} (h : canon3 m = true) : encM9 (dec3 m) = codes9 m := by
  rw [encM9, ents9_dec3 h]

@[expose] noncomputable def encGP (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) : ℕ :=
  encG9 g.2 + 2 ^ 36 * encG2 g.1

theorem split_hi (a b : ℕ) (ha : a < 2 ^ 36) : Nat.shiftRight (a + 2 ^ 36 * b) 36 = b := by
  change (a + 2 ^ 36 * b) >>> 36 = b
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha,
    Nat.zero_add]

theorem split_lo (a b : ℕ) (ha : a < 2 ^ 36) : fldN (a + 2 ^ 36 * b) 0 36 = a := by
  rw [fldN_eq, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem encGP_hi (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) :
    Nat.shiftRight (encGP g) 36 = encG2 g.1 := split_hi _ _ (encG9_lt _)

theorem encGP_lo (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) :
    fldN (encGP g) 0 36 = encG9 g.2 := split_lo _ _ (encG9_lt _)

theorem encP : ClosEnc encGP mP (encGP 1) where
  enc_one := rfl
  enc_mul a b := by
    rw [mP, encGP_lo, encGP_lo, encGP_hi, encGP_hi, ← enc9.enc_mul, ← enc2.enc_mul, encGP,
      Prod.fst_mul, Prod.snd_mul]
    change _ = encG9 (a.2 * b.2) ||| (encG2 (a.1 * b.1) <<< 36)
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (encG9_lt _), Nat.shiftLeft_eq,
      Nat.mul_comm, Nat.add_comm]
  inj a b e := by
    have h1 : encG2 a.1 = encG2 b.1 := by rw [← encGP_hi, e, encGP_hi]
    have h2 : encG9 a.2 = encG9 b.2 := by rw [← encGP_lo, e, encGP_lo]
    exact Prod.ext (enc2.inj h1) (enc9.inj h2)

end CFSG.KC.Misc.G2U

end
