module

public import Certificates.Data.Kernel.S23Inner
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerDataInputs

public section

namespace CFSG.KC.S23

open CFSG.EvenSmallLie.TwoE6.Stroth23Inner CFSG.Monster.B.TwoA.Unitary CFSG.KLie.CT
open CFSG.Monster.B.Co2.Native (actD)

@[expose] def wordActG (n6 : Array (Array ℕ)) (w : List ℕ) (c : ℕ) : ℕ :=
  w.foldl (fun c k => actD 22 n6[k]! c) c

@[expose] def rowsActG (n6 : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  Array.ofFn (n := 22) fun t => wordActG n6 w (1 <<< (t : ℕ))

@[expose] def vecG (n6 : Array (Array ℕ)) (cyc : Array (List ℕ)) (v0 j : ℕ) : ℕ :=
  wordActG n6 cyc[j]! v0

@[expose] def matsDG (n6 : Array (Array ℕ)) (cyc : Array (List ℕ)) : Array (Array ℕ) :=
  cyc.map fun x => rowsActG n6 (deltaWord x)

@[expose] def matsIG (n6 : Array (Array ℕ)) (cyc : Array (List ℕ)) : Array (Array ℕ) :=
  cyc.map fun x => rowsActG n6 x

@[expose] def sumG (R : Array (Array ℕ)) (σ : ℕ) : Array ℕ :=
  Array.ofFn (n := 22) fun t => xorSel (fun j => (R[j]!)[(t : ℕ)]!) σ

open CFSG.KC.F4M (xorN)
open CFSG.KC.Loop (strictN)

private noncomputable def sel (d : ℕ) (r : ℕ → ℕ) (n : ℕ) : ℕ := xorN d fun i => if n.testBit i then r i else 0

private theorem xorN_succ (n : ℕ) (f : ℕ → ℕ) : xorN (n + 1) f = f n ^^^ xorN n f := rfl

private theorem xorN_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n),
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

private theorem xorN_zeros (n : ℕ) : xorN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorN_succ, ih, Nat.xor_zero]

private theorem xorN_xor (n : ℕ) (f g : ℕ → ℕ) :
    xorN n (fun i => f i ^^^ g i) = xorN n f ^^^ xorN n g := by
  induction n with
  | zero => exact (Nat.xor_self 0).symm
  | succ n ih =>
    rw [xorN_succ, xorN_succ, xorN_succ, ih]
    ac_rfl

private theorem lin_zero {h : ℕ → ℕ} (hl : ∀ a b, h (a ^^^ b) = h a ^^^ h b) : h 0 = 0 := by
  have := hl 0 0
  rw [Nat.zero_xor, Nat.xor_self] at this
  exact this

private theorem xorN_lin {h : ℕ → ℕ} (hl : ∀ a b, h (a ^^^ b) = h a ^^^ h b) (n : ℕ)
    (f : ℕ → ℕ) : h (xorN n f) = xorN n (fun i => h (f i)) := by
  induction n with
  | zero => exact lin_zero hl
  | succ n ih => rw [xorN_succ, hl, ih, xorN_succ]

private theorem xorN_swap (n m : ℕ) (F : ℕ → ℕ → ℕ) :
    xorN n (fun i => xorN m (F i)) = xorN m (fun j => xorN n (fun i => F i j)) := by
  induction n with
  | zero => exact (xorN_zeros m).symm
  | succ n ih =>
    rw [xorN_succ, ih, ← xorN_xor]
    rfl

private theorem xorN_single {n t : ℕ} (ht : t < n) (c : ℕ) :
    xorN n (fun s => if s = t then c else 0) = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [xorN_succ]
    by_cases h : t = n
    · subst h
      rw [xorN_congr (g := fun _ => 0) (fun i hi => ite_eq_right (by omega)), xorN_zeros]
      simp
    · rw [ite_eq_right (Ne.symm h), Nat.zero_xor, ih (by omega)]

private theorem xorN_lt {n w : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

private theorem ite_xorN (b : Bool) (n : ℕ) (f : ℕ → ℕ) :
    (if b then xorN n f else 0) = xorN n (fun i => if b then f i else 0) := by
  cases b
  · exact (xorN_zeros n).symm
  · rfl

private theorem sel_congr {d : ℕ} {r r' : ℕ → ℕ} (h : ∀ i < d, r i = r' i) (n : ℕ) :
    sel d r n = sel d r' n :=
  xorN_congr fun i hi => by rw [h i hi]

private theorem sel_zero (d n : ℕ) : sel d (fun _ => 0) n = 0 := by
  unfold sel
  rw [xorN_congr (g := fun _ => 0) (fun i _ => by split <;> rfl), xorN_zeros]

private theorem sel_lt {d w : ℕ} {r : ℕ → ℕ} (h : ∀ i < d, r i < 2 ^ w) (n : ℕ) :
    sel d r n < 2 ^ w :=
  xorN_lt fun i hi => by
    split
    · exact h i hi
    · exact Nat.two_pow_pos w

private theorem sel_rows_xor (d : ℕ) (r r' : ℕ → ℕ) (n : ℕ) :
    sel d (fun t => r t ^^^ r' t) n = sel d r n ^^^ sel d r' n := by
  unfold sel
  rw [← xorN_xor]
  exact xorN_congr fun i _ => by cases n.testBit i <;> simp

private theorem sel_arg_xor (d : ℕ) (r : ℕ → ℕ) (a b : ℕ) :
    sel d r (a ^^^ b) = sel d r a ^^^ sel d r b := by
  unfold sel
  rw [← xorN_xor]
  refine xorN_congr fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp

private theorem sel_lin {h : ℕ → ℕ} (hl : ∀ a b, h (a ^^^ b) = h a ^^^ h b) (d : ℕ)
    (r : ℕ → ℕ) (n : ℕ) : h (sel d r n) = sel d (fun t => h (r t)) n := by
  unfold sel
  rw [xorN_lin hl]
  refine xorN_congr fun i _ => ?_
  split
  · rfl
  · exact lin_zero hl

private theorem sel_swap (d e : ℕ) (c : ℕ → Bool) (q : ℕ → ℕ → ℕ) (n : ℕ) :
    sel d (fun t => xorN e (fun j => if c j then q j t else 0)) n =
      xorN e (fun j => if c j then sel d (q j) n else 0) := by
  unfold sel
  simp only [ite_xorN]
  rw [xorN_swap]
  refine xorN_congr fun j _ => ?_
  cases c j
  · simp only [Bool.false_eq_true, ↓reduceIte, ite_self, xorN_zeros]
  · simp only [↓reduceIte]

private theorem sel_single {d t : ℕ} (ht : t < d) (n : ℕ) :
    sel d (fun s => if s = t then 1 else 0) n = if n.testBit t then 1 else 0 := by
  unfold sel
  rw [xorN_congr (g := fun s => if s = t then (if n.testBit t then 1 else 0) else 0), xorN_single ht]
  intro i _
  by_cases h : i = t
  · subst h
    simp
  · simp [h]

private theorem brec_eq (b : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t b = if b then t else e := by cases b <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem allN_iff {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

private theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by simp only [Nat.beq_eq, decide_eq_true_eq])

private theorem nif_beq (s t : ℕ) :
    Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq s t) = if s = t then 1 else 0 := by
  cases h : Nat.beq s t
  · rw [ite_eq_right (Nat.ne_of_beq_eq_false h)]
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true h)]

private theorem shr_and_one (x t : ℕ) : (x >>> t) &&& 1 = if x.testBit t then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ t) with h | h <;> simp [h]

private theorem fget_eq (X i w : ℕ) : fget X i w = (X >>> (i * w)) &&& (2 ^ w - 1) := by
  change (X >>> (i * w)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft]

private theorem fget_lt (X i w : ℕ) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := w); omega)

private theorem fget_zero (i w : ℕ) : fget 0 i w = 0 := by
  rw [fget_eq, Nat.zero_shiftRight, Nat.zero_and]

private theorem xorSel_eq (f : ℕ → ℕ) (m : ℕ) : xorSel f m = sel 21 f m := by
  have h : ∀ n a, (List.range n).foldl (fun a j => if m.testBit j then a ^^^ f j else a) a =
      a ^^^ sel n f m := by
    intro n
    induction n with
    | zero => exact fun a => (Nat.xor_zero a).symm
    | succ n ih =>
      intro a
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
      unfold sel
      rw [xorN_succ]
      cases m.testBit n
      · simp
      · simp only [↓reduceIte]
        ac_rfl
  unfold xorSel
  rw [h, Nat.zero_xor]

private theorem act_eq (M v : ℕ) : act M v = sel 22 (rowG M) v := by
  unfold act sel
  refine xorN_congr fun i _ => ?_
  rw [brec_eq, bit_eq]

private theorem act_lt (M v : ℕ) : act M v < 2 ^ 22 := by
  rw [act_eq]
  exact sel_lt (fun i _ => fget_lt _ _ _) v

private theorem actGo_eq (rows : Array ℕ) (v : ℕ) : ∀ d acc,
    CFSG.Monster.VisCert.Native.actGo rows v d acc =
      acc ^^^ xorN d (fun i => if v.testBit i then rows[i]! else 0)
  | 0, acc => (Nat.xor_zero acc).symm
  | d + 1, acc => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_eq rows v d, xorN_succ]
    cases v.testBit d
    · simp
    · simp only [↓reduceIte]
      ac_rfl

private theorem actD_eq (rows : Array ℕ) (v : ℕ) : actD 22 rows v = sel 22 (fun i => rows[i]!) v := by
  unfold actD
  rw [actGo_eq, Nat.zero_xor]
  rfl

private def sh (k y : ℕ) : ℕ := y ^^^ (y >>> k)

private theorem sh_xor (k a b : ℕ) : sh k (a ^^^ b) = sh k a ^^^ sh k b := by
  unfold sh
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]
  generalize a.testBit i = x
  generalize b.testBit i = y
  generalize a.testBit (k + i) = z
  generalize b.testBit (k + i) = u
  cases x <;> cases y <;> cases z <;> cases u <;> rfl

private theorem par_xor (a b : ℕ) : par (a ^^^ b) = par a ^^^ par b := by
  have e : ∀ x, par x = sh 1 (sh 2 (sh 4 (sh 8 (sh 16 (x &&& 4294967295))))) &&& 1 := fun _ => rfl
  rw [e, e, e, Nat.and_xor_distrib_right, sh_xor, sh_xor, sh_xor, sh_xor, sh_xor,
    Nat.and_xor_distrib_right]

private theorem and_xor (c a b : ℕ) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) :=
  Nat.and_xor_distrib_right

private theorem par_zero : par 0 = 0 := rfl

private theorem sel_and (c d : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    sel d r n &&& c = sel d (fun t => r t &&& c) n :=
  sel_lin (h := fun x => x &&& c) (and_xor c) d r n

private theorem sel_par (d : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    par (sel d r n) = sel d (fun t => par (r t)) n :=
  sel_lin (h := par) par_xor d r n

private theorem xorN_par (n : ℕ) (f : ℕ → ℕ) : par (xorN n f) = xorN n (fun i => par (f i)) :=
  xorN_lin (h := par) par_xor n f

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
  rw [fget_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
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
      (fun x _ ih k => andB (p x k) (andB (q x k) (ih (Nat.succ k)))) L k = true →
    k + L.length = n ∧ ∀ i (hi : i < L.length), p L[i] (k + i) = true ∧ q L[i] (k + i) = true
  | [], k, h => by
    have : k = n := Nat.eq_of_beq_eq_true h
    exact ⟨by simp [this], fun i hi => absurd hi (by simp)⟩
  | x :: L, k, h => by
    change andB (p x k) (andB (q x k) _) = true at h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨e, hL⟩ := chain2_spec p q n L (k + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i =>
      have := hL i (by simp at hi; omega)
      rw [Nat.add_right_comm, Nat.add_assoc] at this
      simpa [Nat.add_comm 1 i] using this

private theorem bindM_spec (N6 : ℕ) : ∀ (L : List (Array ℕ)) (k : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun k => Nat.beq k 17)
      (fun r _ ih k => andB (bindRow (mat N6 k) r.toList) (ih (Nat.succ k))) L k = true →
    k + L.length = 17 ∧ ∀ i (hi : i < L.length), bindRow (mat N6 (k + i)) L[i].toList = true
  | [], k, h => by
    have : k = 17 := Nat.eq_of_beq_eq_true h
    exact ⟨by simp [this], fun i hi => absurd hi (by simp)⟩
  | x :: L, k, h => by
    change andB (bindRow (mat N6 k) x.toList) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h3⟩ := h
    obtain ⟨e, hL⟩ := bindM_spec N6 L (k + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      have := hL i (by simp at hi; omega)
      rw [Nat.add_right_comm, Nat.add_assoc] at this
      simpa [Nat.add_comm 1 i] using this

set_option exponentiation.threshold 8228 in
private theorem n6_rows {N6 : ℕ} {n6 : Array (Array ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) (k : ℕ) {t : ℕ} (ht : t < 22) :
    n6[k]![t]! = rowG (mat N6 k) t := by
  obtain ⟨e, hL⟩ := bindM_spec N6 n6.toList 0 hM
  simp only [Nat.zero_add, Array.length_toList] at e hL
  by_cases hk : k < 17
  · have hk' : k < n6.size := by
      rw [e]
      exact hk
    have hr := chain2_spec (fun x _ => Nat.blt x 4194304) (fun x t => Nat.beq x (rowG (mat N6 k) t))
      22 (n6[k]'hk').toList 0 (hL k hk')
    simp only [Nat.zero_add, Array.length_toList] at hr
    have ht' : t < (n6[k]'hk').size := by omega
    rw [getElem!_pos n6 k hk', getElem!_pos _ t ht']
    have := (hr.2 t ht').2
    simpa using Nat.eq_of_beq_eq_true this
  · have hk' : ¬ k < n6.size := by
      rw [e]
      exact hk
    rw [getElem!_neg n6 k hk']
    have h0 : mat N6 k = 0 := by
      unfold mat
      rw [fget_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt, Nat.zero_and]
      exact Nat.lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide)
        (Nat.le_trans (by decide : 8228 ≤ 17 * 484) (Nat.mul_le_mul_right 484 (Nat.le_of_not_lt hk))))
    unfold rowG
    rw [h0, fget_zero]
    rfl

private theorem rowG_lt (M t : ℕ) : rowG M t < 2 ^ 22 := fget_lt M t 22

private theorem n6_act {N6 : ℕ} {n6 : Array (Array ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) (k c : ℕ) : act (mat N6 k) c = actD 22 n6[k]! c := by
  rw [act_eq, actD_eq]
  exact sel_congr (fun i hi => (n6_rows hN hM k hi).symm) c

private theorem wact_eq {N6 : ℕ} {n6 : Array (Array ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) : ∀ (w : List ℕ) (c : ℕ), wact N6 w c = wordActG n6 w c
  | [], _ => rfl
  | k :: w, c => by
    have e : wact N6 (k :: w) c = wact N6 w (act (mat N6 k) c) := strictN_eq _ _
    rw [e, wact_eq hN hM w, n6_act hN hM]
    rfl

private theorem wordActG_lt {N6 : ℕ} {n6 : Array (Array ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) : ∀ (w : List ℕ) {c : ℕ}, c < 2 ^ 22 → wordActG n6 w c < 2 ^ 22
  | [], _, hc => hc
  | k :: w, c, _ => by
    have e : wordActG n6 (k :: w) c = wordActG n6 w (actD 22 n6[k]! c) := rfl
    rw [e]
    refine wordActG_lt hN hM w ?_
    rw [← n6_act hN hM]
    exact act_lt _ _

private theorem delta_eq : ∀ w : List ℕ, delta w = deltaWord w
  | [] => rfl
  | k :: w => by
    change Bool.rec (motive := fun _ => List ℕ) (k :: delta w) (2 :: 1 :: 1 :: 4 :: delta w)
      (Nat.beq k 4) = (k :: w).flatMap deltaLetter
    rw [List.flatMap_cons, delta_eq w]
    cases h : Nat.beq k 4
    · have : k ≠ 4 := Nat.ne_of_beq_eq_false h
      simp [deltaLetter, this, deltaWord]
    · have : k = 4 := Nat.eq_of_beq_eq_true h
      simp [deltaLetter, this, deltaWord]

private theorem getW_eq : ∀ (L : List (List ℕ)) (j : ℕ) (hj : j < L.length), getW L j = L[j]
  | [], _, hj => absurd hj (by simp)
  | x :: L, 0, _ => rfl
  | x :: L, j + 1, hj => by
    change getW L j = _
    rw [getW_eq L j (by simp at hj; omega)]
    rfl

private theorem getElem!_ofFn22 (f : Fin 22 → ℕ) {t : ℕ} (ht : t < 22) :
    (Array.ofFn f)[t]! = f ⟨t, ht⟩ := by
  rw [getElem!_pos (Array.ofFn f) t (by simpa using ht), Array.getElem_ofFn]

private theorem cyc_word {cyc : Array (List ℕ)} (hsz : cyc.size = 21) {j : ℕ} (hj : j < 21) :
    getW cyc.toList j = cyc[j]! := by
  rw [getW_eq _ j (by simp [hsz, hj]), getElem!_pos cyc j (by omega)]
  rfl

private theorem vecs_get {N6 : ℕ} {n6 : Array (Array ℕ)} {cyc : Array (List ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) (hsz : cyc.size = 21) {v0 : ℕ} (hv : v0 < 2 ^ 22) {j : ℕ}
    (hj : j < 21) : fget (vecs N6 cyc.toList v0) j 22 = vecG n6 cyc v0 j := by
  have hb : ∀ j < 21, wact N6 (getW cyc.toList j) v0 < 2 ^ 22 := fun j _ => by
    rw [wact_eq hN hM]
    exact wordActG_lt hN hM _ hv
  have e : fget (vecs N6 cyc.toList v0) j 22 = wact N6 (getW cyc.toList j) v0 :=
    fget_pack (w := 22) (n := 21) (F := fun j => wact N6 (getW cyc.toList j) v0) hb hj
  rw [e, wact_eq hN hM, cyc_word hsz hj]
  rfl

private theorem xsel_eq {N6 : ℕ} {n6 : Array (Array ℕ)} {cyc : Array (List ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) (hsz : cyc.size = 21) {v0 : ℕ} (hv : v0 < 2 ^ 22) (m : ℕ) :
    xsel (vecs N6 cyc.toList v0) m = xorSel (vecG n6 cyc v0) m := by
  rw [xorSel_eq]
  unfold xsel
  refine xorN_congr fun j hj => ?_
  rw [brec_eq, bit_eq, vecs_get hN hM hsz hv hj]

set_option exponentiation.threshold 484 in
private theorem mats_rows {N6 : ℕ} {n6 : Array (Array ℕ)} {cyc : Array (List ℕ)}
    (hN : N6 < 2 ^ 8228) (hM : bindM N6 n6 = true) (hsz : cyc.size = 21) (dl : Bool)
    (wd : List ℕ → List ℕ)
    (hwd : ∀ x, Bool.rec (motive := fun _ => List ℕ) x (delta x) dl = wd x)
    {j t : ℕ} (hj : j < 21) (ht : t < 22) :
    rowG (matJ (mats N6 cyc.toList dl) j) t = ((cyc.map fun x => rowsActG n6 (wd x))[j]!)[t]! := by
  have hb : ∀ w : List ℕ, ∀ s < 22, wact N6 w (pw2 s) < 2 ^ 22 := fun w s hs => by
    rw [wact_eq hN hM]
    exact wordActG_lt hN hM _ (by
      change 1 <<< s < 2 ^ 22
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by omega) hs)
  have hrow : ∀ w : List ℕ, ∀ t < 22, rowG (rowsW N6 w) t = wordActG n6 w (1 <<< t) := by
    intro w t ht
    have e : rowG (rowsW N6 w) t = wact N6 w (pw2 t) :=
      fget_pack (w := 22) (n := 22) (F := fun t => wact N6 w (pw2 t)) (hb w) ht
    rw [e, wact_eq hN hM]
    rfl
  have hRs : ∀ w : List ℕ, rowsW N6 w < 2 ^ 484 := fun w =>
    pack_lt (w := 22) (n := 22) (F := fun t => wact N6 w (pw2 t)) (hb w) (by decide)
  have hmat : matJ (mats N6 cyc.toList dl) j = rowsW N6 (Bool.rec (motive := fun _ => List ℕ)
      (getW cyc.toList j) (delta (getW cyc.toList j)) dl) :=
    fget_pack (w := 484) (n := 21) (F := fun j => rowsW N6 (Bool.rec (motive := fun _ => List ℕ)
      (getW cyc.toList j) (delta (getW cyc.toList j)) dl)) (fun j _ => hRs _) hj
  rw [hmat, cyc_word hsz hj, hwd, hrow _ t ht,
    getElem!_pos (cyc.map fun x => rowsActG n6 (wd x)) j (by simp [hsz, hj]), Array.getElem_map,
    ← getElem!_pos cyc j (by omega)]
  unfold rowsActG
  rw [getElem!_ofFn22 _ ht]

private noncomputable def lmS (Rs σ t : ℕ) : ℕ :=
  xorN 21 fun j => Bool.rec (motive := fun _ => ℕ) 0 (rowG (matJ Rs j) t) (bit σ j)

private noncomputable def lmL (N6 Rs G i t : ℕ) : ℕ :=
  (xorN 21 fun j => Bool.rec (motive := fun _ => ℕ) 0 (rowG (matJ Rs j) t) (bit (fget G i 22) j)) ^^^
    act (mat N6 0) (rowG (matJ Rs i) t)

private theorem lmS_lt (Rs σ t : ℕ) : lmS Rs σ t < 2 ^ 22 :=
  xorN_lt fun j _ => by
    rw [brec_eq]
    split
    · exact rowG_lt _ _
    · exact Nat.two_pow_pos 22

private theorem lmL_lt (N6 Rs G i t : ℕ) : lmL N6 Rs G i t < 2 ^ 22 := by
  unfold lmL
  refine Nat.xor_lt_two_pow (xorN_lt fun j _ => ?_) (act_lt _ _)
  rw [brec_eq]
  split
  · exact rowG_lt _ _
  · exact Nat.two_pow_pos 22

set_option exponentiation.threshold 484 in
private theorem linMaps_rows (N6 Rs σ G : ℕ) :
    (∀ t < 22, rowG (matJ (linMaps N6 Rs σ G) 0) t = lmS Rs σ t) ∧
    (∀ i < 21, ∀ t < 22, rowG (matJ (linMaps N6 Rs σ G) (i + 1)) t = lmL N6 Rs G i t) := by
  have hA : (orN 22 fun t => lmS Rs σ t <<< (22 * t)) < 2 ^ 484 :=
    pack_lt (w := 22) (n := 22) (F := fun t => lmS Rs σ t) (fun t _ => lmS_lt _ _ _) (by decide)
  have hB : ∀ i < 21, (orN 22 fun t => lmL N6 Rs G i t <<< (22 * t)) < 2 ^ 484 := fun i _ =>
    pack_lt (w := 22) (n := 22) (F := fun t => lmL N6 Rs G i t) (fun t _ => lmL_lt _ _ _ _ _)
      (by decide)
  have e : linMaps N6 Rs σ G = (orN 22 fun t => lmS Rs σ t <<< (22 * t)) |||
      orN 21 (fun i => (orN 22 fun t => lmL N6 Rs G i t <<< (22 * t)) <<< (484 * (i + 1))) := rfl
  have hF := fld_or (fld_one hA) (fld_orN (n := 21)
    (G := fun i m => if m = i + 1 then orN 22 (fun t => lmL N6 Rs G i t <<< (22 * t)) else 0)
    (fun i hi => fld_term (hB i hi) (i + 1)))
  rw [← e] at hF
  have h0 := orN_ite (fun i => orN 22 (fun t => lmL N6 Rs G i t <<< (22 * t))) 1 0 21
  have g0 : ((if (0 : ℕ) = 0 then (orN 22 fun t => lmS Rs σ t <<< (22 * t)) else 0) |||
      orN 21 (fun i => if (0 : ℕ) = i + 1 then orN 22 (fun t => lmL N6 Rs G i t <<< (22 * t))
        else 0)) = orN 22 fun t => lmS Rs σ t <<< (22 * t) := by
    rw [h0, ite_eq_left rfl, ite_eq_right (by omega), Nat.or_zero]
  refine ⟨fun t ht => ?_, fun i hi t ht => ?_⟩
  · have hm : matJ (linMaps N6 Rs σ G) 0 = orN 22 fun t => lmS Rs σ t <<< (22 * t) := by
      unfold matJ
      rw [fget_of_fld hF (by rw [g0]; exact hA), g0]
    unfold rowG
    rw [hm]
    exact fget_pack (w := 22) (n := 22) (F := fun t => lmS Rs σ t) (fun t _ => lmS_lt _ _ _) ht
  · have h1 := orN_ite (fun i => orN 22 (fun t => lmL N6 Rs G i t <<< (22 * t))) 1 (i + 1) 21
    have g1 : ((if i + 1 = 0 then (orN 22 fun t => lmS Rs σ t <<< (22 * t)) else 0) |||
        orN 21 (fun j => if i + 1 = j + 1 then orN 22 (fun t => lmL N6 Rs G j t <<< (22 * t))
          else 0)) = orN 22 fun t => lmL N6 Rs G i t <<< (22 * t) := by
      rw [h1, ite_eq_right (by omega), ite_eq_left (by omega), Nat.zero_or, Nat.add_sub_cancel]
    have hm : matJ (linMaps N6 Rs σ G) (i + 1) = orN 22 fun t => lmL N6 Rs G i t <<< (22 * t) := by
      unfold matJ
      rw [fget_of_fld hF (by rw [g1]; exact hB i hi), g1]
    unfold rowG
    rw [hm]
    exact fget_pack (w := 22) (n := 22) (F := fun t => lmL N6 Rs G i t) (fun t _ => lmL_lt _ _ _ _ _)
      ht

private theorem act_lin (M a b : ℕ) : act M (a ^^^ b) = act M a ^^^ act M b := by
  rw [act_eq, act_eq, act_eq, sel_arg_xor]

private theorem sel_act (M d : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    act M (sel d r n) = sel d (fun t => act M (r t)) n :=
  sel_lin (h := act M) (act_lin M) d r n

private theorem sumG_get (R : Array (Array ℕ)) (σ : ℕ) {t : ℕ} (ht : t < 22) :
    (sumG R σ)[t]! = xorSel (fun j => (R[j]!)[t]!) σ := by
  unfold sumG
  rw [getElem!_ofFn22 _ ht]

private theorem maps_eq {N6 : ℕ} {n6 : Array (Array ℕ)} (hN : N6 < 2 ^ 8228)
    (hM : bindM N6 n6 = true) {Rs σ G : ℕ} {R : Array (Array ℕ)}
    (hR : ∀ j < 21, ∀ t < 22, rowG (matJ Rs j) t = (R[j]!)[t]!) (n : ℕ) :
    sel 22 (rowG (matJ (linMaps N6 Rs σ G) 0)) n = actD 22 (sumG R σ) n ∧
    ∀ i < 21, sel 22 (rowG (matJ (linMaps N6 Rs σ G) (i + 1))) n =
      xorSel (fun j => actD 22 R[j]! n) (fget G i 22) ^^^ actD 22 n6[0]! (actD 22 R[i]! n) := by
  obtain ⟨h0, h1⟩ := linMaps_rows N6 Rs σ G
  refine ⟨?_, fun i hi => ?_⟩
  · rw [actD_eq]
    refine sel_congr (fun t ht => ?_) n
    rw [h0 t ht, sumG_get R σ ht, xorSel_eq]
    unfold lmS sel
    refine xorN_congr fun j hj => ?_
    rw [brec_eq, bit_eq, hR j hj t ht]
  · rw [sel_congr (fun t ht => h1 i hi t ht) n]
    unfold lmL
    have e1 : ∀ t, xorN 21 (fun j => Bool.rec (motive := fun _ => ℕ) 0 (rowG (matJ Rs j) t)
        (bit (fget G i 22) j)) =
        xorN 21 (fun j => if (fget G i 22).testBit j then rowG (matJ Rs j) t else 0) := fun t =>
      xorN_congr fun j _ => by rw [brec_eq, bit_eq]
    simp only [e1]
    rw [sel_rows_xor, sel_swap, (sel_act (mat N6 0) 22 (fun t => rowG (matJ Rs i) t) n).symm,
      n6_act hN hM, actD_eq R[i]!, sel_congr (fun t ht => hR i hi t ht) n, xorSel_eq]
    congr 1
    refine xorN_congr fun j hj => ?_
    simp only [actD_eq]
    rw [sel_congr (fun t ht => hR j hj t ht) n]

private theorem comb_eq (Ms U n : ℕ) :
    xorN 22 (fun m => par (sel 22 (rowG (matJ Ms m)) n &&& fget U m 22)) = sel 22 (combAt Ms U) n := by
  have e1 : ∀ m, par (sel 22 (rowG (matJ Ms m)) n &&& fget U m 22) =
      sel 22 (fun s => par (rowG (matJ Ms m) s &&& fget U m 22)) n := fun m => by
    rw [sel_and, sel_par]
  simp only [e1]
  unfold sel
  rw [xorN_swap]
  refine xorN_congr fun s _ => ?_
  rw [← ite_xorN, ← xorN_par]
  rfl

private theorem comb_sol {Ms U rhs n : ℕ} (h0 : sel 22 (rowG (matJ Ms 0)) n = rhs)
    (h1 : ∀ i < 21, sel 22 (rowG (matJ Ms (i + 1))) n = 0) :
    xorN 22 (fun m => par (sel 22 (rowG (matJ Ms m)) n &&& fget U m 22)) =
      par (rhs &&& fget U 0 22) := by
  rw [xorN_congr (g := fun m => if m = 0 then par (rhs &&& fget U 0 22) else 0), xorN_single (by omega)]
  intro m hm
  rcases m with _ | i
  · rw [h0]
    rfl
  · rw [h1 i (by omega), Nat.zero_and, par_zero]
    rfl

private theorem infeas_sound {Ms U rhs n : ℕ} (h : infeasOK Ms U rhs = true)
    (h0 : sel 22 (rowG (matJ Ms 0)) n = rhs) (h1 : ∀ i < 21, sel 22 (rowG (matJ Ms (i + 1))) n = 0) :
    False := by
  unfold infeasOK at h
  rw [andB_eq, Bool.and_eq_true, allN_iff] at h
  obtain ⟨hc, hp⟩ := h
  have e := comb_eq Ms U n
  rw [comb_sol h0 h1, sel_congr (r' := fun _ => 0) (fun s hs => Nat.eq_of_beq_eq_true (hc s hs)),
    sel_zero] at e
  have hp' : par (Nat.land rhs (fget U 0 22)) = 1 := Nat.eq_of_beq_eq_true hp
  change par (rhs &&& fget U 0 22) = 1 at hp'
  omega

private theorem uniq_sound {Ms C rhs sol n : ℕ} (h : uniqOK Ms C rhs sol = true)
    (h0 : sel 22 (rowG (matJ Ms 0)) n = rhs) (h1 : ∀ i < 21, sel 22 (rowG (matJ Ms (i + 1))) n = 0)
    {t : ℕ} (ht : t < 22) : n.testBit t = sol.testBit t := by
  unfold uniqOK at h
  have h2 := allN_iff.1 h t ht
  change andB _ _ = true at h2
  rw [andB_eq, Bool.and_eq_true, allN_iff] at h2
  obtain ⟨hc, hp⟩ := h2
  have e := comb_eq Ms (fget C t 484) n
  rw [comb_sol h0 h1, sel_congr (r' := fun s => if s = t then 1 else 0) (fun s hs =>
    (Nat.eq_of_beq_eq_true (hc s hs)).trans (nif_beq s t)), sel_single ht] at e
  have hp' := Nat.eq_of_beq_eq_true hp
  change par (rhs &&& fget (fget C t 484) 0 22) = (sol >>> t) &&& 1 at hp'
  rw [hp', shr_and_one] at e
  cases h3 : n.testBit t <;> cases h4 : sol.testBit t <;> simp_all

private theorem indep_sound {V W : ℕ} (h : indepOK V W = true) {m : ℕ} (hm : m < 2 ^ 21)
    (h0 : sel 21 (fun i => fget V i 22) m = 0) : m = 0 := by
  unfold indepOK at h
  have hb : ∀ j < 21, m.testBit j = false := by
    intro j hj
    have e : par (sel 21 (fun i => fget V i 22) m &&& fget W j 22) =
        sel 21 (fun i => par (fget V i 22 &&& fget W j 22)) m := by
      rw [sel_and, sel_par]
    rw [h0, Nat.zero_and, par_zero, sel_congr (r := fun i => par (fget V i 22 &&& fget W j 22))
      (r' := fun i => if i = j then 1 else 0)
      (fun i hi => (Nat.eq_of_beq_eq_true (allN_iff.1 (allN_iff.1 h i hi) j hj)).trans
        (nif_beq i j)), sel_single hj] at e
    cases h3 : m.testBit j
    · rfl
    · rw [h3] at e
      simp at e
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < 21
  · exact hb j hj
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem bindA_get {P w n : ℕ} {A : Array ℕ} (h : bindA P w n A = true) {i : ℕ} (hi : i < n) :
    A[i]! = fget P i w := by
  obtain ⟨e, hL⟩ := chain2_spec (fun x _ => Nat.blt x (pw2 w)) (fun x k => Nat.beq x (fget P k w)) n
    A.toList 0 h
  simp only [Nat.zero_add, Array.length_toList] at e hL
  have hi' : i < A.size := by omega
  rw [getElem!_pos A i hi']
  have := (hL i hi').2
  simpa using Nat.eq_of_beq_eq_true this

private theorem mats_lt {Rs : ℕ} {R : Array (Array ℕ)} (hR : ∀ j < 21, ∀ t < 22, rowG (matJ Rs j) t = (R[j]!)[t]!) :
    ∀ j < 21, ∀ t < 22, (R[j]!)[t]! < 2 ^ 22 := fun j hj t ht => by
  rw [← hR j hj t ht]
  exact rowG_lt _ _

theorem soundD (n6 : Array (Array ℕ)) (cyc : Array (List ℕ)) (g0 : Array ℕ) (cycL : List (List ℕ))
    (N6 GD CD : Nat) (hN : N6 < 2 ^ 8228) (hsz : cyc.size = 21) (hc : cyc.toList = cycL)
    (hb : andB (bindM N6 n6) (bindA GD 22 21 g0) = true) (hd : checkD N6 GD CD cycL = true) :
    (xorSel (vecG n6 cyc 155) 3112 = 6144)
    ∧ (∀ i < 21, actD 22 n6[0]! (vecG n6 cyc 155 i) = xorSel (vecG n6 cyc 155) g0[i]!)
    ∧ (∀ j < 21, ∀ t < 22, ((matsDG n6 cyc)[j]!)[t]! < 2 ^ 22)
    ∧ (∀ n < 2 ^ 22, actD 22 (sumG (matsDG n6 cyc) 3112) n = 6144 → ∃ i < 21, xorSel (fun j =>
      actD 22 (matsDG n6 cyc)[j]! n) g0[i]! ≠ actD 22 n6[0]! (actD 22 (matsDG n6 cyc)[i]! n)) := by
  subst hc
  rw [andB_eq, Bool.and_eq_true] at hb
  obtain ⟨hM, hG⟩ := hb
  unfold checkD at hd
  simp only [strictB_eq, andB_eq, Bool.and_eq_true] at hd
  obtain ⟨d1, d2, d3⟩ := hd
  have hv : (155 : ℕ) < 2 ^ 22 := by decide
  have hR : ∀ j < 21, ∀ t < 22, rowG (matJ (mats N6 cyc.toList true) j) t =
      ((matsDG n6 cyc)[j]!)[t]! := fun j hj t ht =>
    mats_rows hN hM hsz true deltaWord (fun x => delta_eq x) hj ht
  refine ⟨?_, ?_, mats_lt hR, ?_⟩
  · rw [← xsel_eq hN hM hsz hv]
    exact Nat.eq_of_beq_eq_true d1
  · intro i hi
    have := Nat.eq_of_beq_eq_true (allN_iff.1 d2 i hi)
    rw [n6_act hN hM, vecs_get hN hM hsz hv hi, xsel_eq hN hM hsz hv, ← bindA_get hG hi] at this
    exact this
  · intro n _ hS
    refine Classical.byContradiction fun hcon => ?_
    have hall : ∀ i < 21, xorSel (fun j => actD 22 (matsDG n6 cyc)[j]! n) g0[i]! =
        actD 22 n6[0]! (actD 22 (matsDG n6 cyc)[i]! n) := fun i hi =>
      Classical.byContradiction fun hne => hcon ⟨i, hi, hne⟩
    obtain ⟨m0, m1⟩ := maps_eq (σ := 3112) (G := GD) hN hM hR n
    refine infeas_sound d3 (rhs := 6144) (n := n) ?_ ?_
    · rw [m0, hS]
    · intro i hi
      rw [m1 i hi, ← bindA_get hG hi, hall i hi, Nat.xor_self]

theorem soundI (n6 : Array (Array ℕ)) (cyc : Array (List ℕ)) (g0 uM uB : Array ℕ)
    (cycL : List (List ℕ)) (N6 GI CI WI UM U20 : Nat) (hN : N6 < 2 ^ 8228) (hsz : cyc.size = 21)
    (hc : cyc.toList = cycL)
    (hb : andB (bindM N6 n6) (andB (bindA GI 22 21 g0) (andB (bindA UM 22 20 uM)
      (bindA U20 22 20 uB))) = true)
    (hi : checkI N6 GI CI WI UM U20 cycL = true) :
    (xorSel (vecG n6 cyc 714762) 3989 = 6144)
    ∧ (∀ i < 21, actD 22 n6[0]! (vecG n6 cyc 714762 i) = xorSel (vecG n6 cyc 714762) g0[i]!)
    ∧ (∀ j < 21, ∀ t < 22, ((matsIG n6 cyc)[j]!)[t]! < 2 ^ 22)
    ∧ (∀ m < 2 ^ 21, xorSel (vecG n6 cyc 714762) m = 0 → m = 0)
    ∧ (∀ n < 2 ^ 22, actD 22 (sumG (matsIG n6 cyc) 3989) n = 6144 → (∀ i < 21, xorSel (fun j =>
      actD 22 (matsIG n6 cyc)[j]! n) g0[i]! = actD 22 n6[0]! (actD 22 (matsIG n6 cyc)[i]! n)) →
      n = 714762)
    ∧ (∀ t < 20, xorSel (vecG n6 cyc 714762) uM[t]! = uB[t]!) := by
  subst hc
  simp only [andB_eq, Bool.and_eq_true] at hb
  obtain ⟨hM, hG, hUM, hU20⟩ := hb
  unfold checkI at hi
  simp only [strictB_eq, andB_eq, Bool.and_eq_true] at hi
  obtain ⟨d1, d2, d3, d4, d5⟩ := hi
  have hv : (714762 : ℕ) < 2 ^ 22 := by decide
  have hR : ∀ j < 21, ∀ t < 22, rowG (matJ (mats N6 cyc.toList false) j) t =
      ((matsIG n6 cyc)[j]!)[t]! := fun j hj t ht =>
    mats_rows hN hM hsz false (fun x => x) (fun _ => rfl) hj ht
  refine ⟨?_, ?_, mats_lt hR, ?_, ?_, ?_⟩
  · rw [← xsel_eq hN hM hsz hv]
    exact Nat.eq_of_beq_eq_true d1
  · intro i hi
    have := Nat.eq_of_beq_eq_true (allN_iff.1 d2 i hi)
    rw [n6_act hN hM, vecs_get hN hM hsz hv hi, xsel_eq hN hM hsz hv, ← bindA_get hG hi] at this
    exact this
  · intro m hm h0
    refine indep_sound d3 hm ?_
    rw [← h0, xorSel_eq]
    exact sel_congr (fun i hi => vecs_get hN hM hsz hv hi) m
  · intro n hn hS hall
    obtain ⟨m0, m1⟩ := maps_eq (σ := 3989) (G := GI) hN hM hR n
    have e0 : sel 22 (rowG (matJ (linMaps N6 (mats N6 cyc.toList false) 3989 GI) 0)) n = 6144 := by
      rw [m0, hS]
    have e1 : ∀ i < 21, sel 22 (rowG (matJ (linMaps N6 (mats N6 cyc.toList false) 3989 GI)
        (i + 1))) n = 0 := by
      intro i hi
      rw [m1 i hi, ← bindA_get hG hi, hall i hi, Nat.xor_self]
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < 22
    · exact uniq_sound d4 e0 e1 ht
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))]
  · intro t ht
    have := Nat.eq_of_beq_eq_true (allN_iff.1 d5 t ht)
    rw [xsel_eq hN hM hsz hv, ← bindA_get hUM (i := t) (by omega), ← bindA_get hU20 (i := t) (by omega)] at this
    exact this

end CFSG.KC.S23

end
