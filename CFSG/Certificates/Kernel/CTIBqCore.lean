module

public import Certificates.Data.Kernel.CTIBqBind

public section

namespace CFSG.KC.CTIBq

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.S23 CFSG.Monster.B.CTIB.Native

namespace Aux

theorem brec_eq (b : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t b = if b then t else e := by cases b <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by simp only [Nat.beq_eq, decide_eq_true_eq])

theorem blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])

theorem fget_eq (X i w : Nat) : fget X i w = (X >>> (i * w)) &&& (2 ^ w - 1) := by
  change (X >>> (i * w)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft]

theorem fget_lt (X i w : Nat) : fget X i w < 2 ^ w := by
  rw [fget_eq]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := w); omega)

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem xorN_succ (n : Nat) (f : Nat → Nat) : xorN (n + 1) f = f n ^^^ xorN n f := rfl

theorem xorN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n),
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem xorN_zeros (n : Nat) : xorN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorN_succ, ih, Nat.xor_zero]

theorem lin_zero {h : Nat → Nat} (hl : ∀ a b, h (a ^^^ b) = h a ^^^ h b) : h 0 = 0 := by
  have := hl 0 0
  rw [Nat.zero_xor, Nat.xor_self] at this
  exact this

theorem xorN_lin {h : Nat → Nat} (hl : ∀ a b, h (a ^^^ b) = h a ^^^ h b) (n : Nat)
    (f : Nat → Nat) : h (xorN n f) = xorN n (fun i => h (f i)) := by
  induction n with
  | zero => exact lin_zero hl
  | succ n ih => rw [xorN_succ, hl, ih, xorN_succ]

theorem xorN_lt {n w : Nat} {f : Nat → Nat} (h : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih =>
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n (Nat.lt_succ_self n)) (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

theorem xorN_add (n m : Nat) (f : Nat → Nat) :
    xorN (n + m) f = xorN n f ^^^ xorN m (fun i => f (n + i)) := by
  induction m with
  | zero => exact (Nat.xor_zero _).symm
  | succ m ih =>
    rw [← Nat.add_assoc, xorN_succ, ih, xorN_succ]
    ac_rfl

@[expose] def Fld (w X : Nat) (g : Nat → Nat) : Prop :=
  ∀ i k, k < w → X.testBit (w * i + k) = (g i).testBit k

theorem fld_congr {w X : Nat} {g g' : Nat → Nat} (h : Fld w X g) (e : ∀ i, g i = g' i) :
    Fld w X g' := fun i k hk => by rw [h i k hk, e]

theorem fld_or {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ||| B) (fun i => g i ||| h i) := by
  intro i k hk
  rw [Nat.testBit_or, hA i k hk, hB i k hk, Nat.testBit_or]

theorem fld_one {w v : Nat} (hv : v < 2 ^ w) : Fld w v (fun i => if i = 0 then v else 0) := by
  intro i k hk
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h1 : w ≤ w * i + k := Nat.le_trans (Nat.le_mul_of_pos_right w hi) (Nat.le_add_right _ _)
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) h1))

theorem fld_shl {w B : Nat} {h : Nat → Nat} (s : Nat) (hB : Fld w B h) :
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

theorem fld_term {w F : Nat} (hF : F < 2 ^ w) (s : Nat) :
    Fld w (F <<< (w * s)) (fun i => if i = s then F else 0) := by
  refine fld_congr (fld_shl s (fld_one hF)) fun i => ?_
  by_cases h : i = s
  · subst h
    simp
  · by_cases h2 : s ≤ i
    · have : i - s ≠ 0 := by omega
      simp [h, h2, this]
    · simp [h, h2]

theorem fld_orN {w n : Nat} {T : Nat → Nat} {G : Nat → Nat → Nat} (h : ∀ j < n, Fld w (T j) (G j)) :
    Fld w (orN n T) (fun i => orN n (fun j => G j i)) := by
  induction n with
  | zero =>
    intro i k _
    change Nat.testBit 0 _ = Nat.testBit 0 _
    rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ n ih =>
    exact fld_or (h n (Nat.lt_succ_self n)) (ih fun j hj => h j (Nat.lt_succ_of_lt hj))

theorem fget_of_fld {w X i : Nat} {g : Nat → Nat} (hX : Fld w X g) (hg : g i < 2 ^ w) :
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

theorem orN_ite (F : Nat → Nat) (o i : Nat) : ∀ n,
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

theorem fget_pack {w n : Nat} {F : Nat → Nat} (hF : ∀ j < n, F j < 2 ^ w) {i : Nat} (hi : i < n) :
    fget (orN n fun j => F j <<< (w * j)) i w = F i := by
  have h := fld_orN (w := w) (n := n) (G := fun j i => if i = j then F j else 0)
    (fun j hj => fld_term (hF j hj) j)
  have e := orN_ite F 0 i n
  simp only [Nat.add_zero, Nat.sub_zero, Nat.zero_le, true_and] at e
  rw [fget_of_fld h, e, ite_eq_left hi]
  rw [e, ite_eq_left hi]
  exact hF i hi

theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenL t) = t.length + 1
    rw [ih]

@[expose] noncomputable def bindLG (P w : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget P k w)) (ih (Nat.succ k)))) l

theorem bindLG_get (P w : Nat) : ∀ (l : List Nat) (k : Nat), bindLG P w l k = true →
    ∀ i (hi : i < l.length), l[i] < 2 ^ w ∧ l[i] = fget P (k + i) w
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: t, k, h, i, hi => by
    have h' : andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget P k w)) (bindLG P w t (Nat.succ k)))
        = true := h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    cases i with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [blt_eq, decide_eq_true_eq, pw2_eq] at h1
        exact h1
      · exact Nat.eq_of_beq_eq_true h2
    | succ i =>
      have := bindLG_get P w t (Nat.succ k) h3 i (by simpa using hi)
      rw [Nat.succ_add] at this
      simpa [Nat.add_assoc, Nat.add_comm 1 i, Nat.succ_add] using this

theorem bindL_get {P w : Nat} {l : List Nat} (h : bindL P w l = true) {i : Nat}
    (hi : i < l.length) : l[i] < 2 ^ w ∧ l[i] = fget P i w := by
  have := bindLG_get P w l 0 h i hi
  simpa using this

theorem bindL_getD {P w : Nat} {l : List Nat} (h : bindL P w l = true) {i : Nat}
    (hi : i < l.length) : l.toArray.getD i 0 = fget P i w := by
  have := (bindL_get h hi).2
  simpa [Array.getD, hi] using this

theorem bindL_lt {P w : Nat} {l : List Nat} (h : bindL P w l = true) {i : Nat}
    (hi : i < l.length) : l.toArray.getD i 0 < 2 ^ w := by
  have := (bindL_get h hi)
  simpa [Array.getD, hi] using this.1

theorem M22_sub (j : Nat) (hj : j < 22) : M22 - maskN (j + 1) = (2 ^ (21 - j) - 1) <<< (j + 1) := by
  have h22 : M22 = 2 ^ 22 - 1 := by decide
  have hA : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ (21 - j) := Nat.one_le_two_pow
  have hAB : 2 ^ 22 = 2 ^ (j + 1) * 2 ^ (21 - j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h1 : 2 ^ (j + 1) ≤ 2 ^ (j + 1) * 2 ^ (21 - j) := Nat.le_mul_of_pos_right _ hB
  have h2 : (2 ^ (21 - j) - 1) * 2 ^ (j + 1) = 2 ^ (j + 1) * 2 ^ (21 - j) - 2 ^ (j + 1) := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
  have hm : maskN (j + 1) = 2 ^ (j + 1) - 1 := by
    unfold maskN
    rw [pw2_eq]
    rfl
  rw [Nat.shiftLeft_eq, h2, h22, hAB, hm]
  omega

theorem testBit_gu (GR j n : Nat) (hj : j < 22) :
    (gu GR j).testBit n = ((fget GR j 22).testBit n && decide (j < n) && decide (n < 22)) := by
  change ((fget GR j 22) &&& (M22 - maskN (j + 1))).testBit n = _
  rw [M22_sub j hj, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h1 : j < n
  · by_cases h2 : n < 22
    · have : n - (j + 1) < 21 - j := by omega
      simp [h1, h2, this, Nat.succ_le_of_lt h1]
    · have : ¬ n - (j + 1) < 21 - j := by omega
      simp [h1, h2, this, Nat.succ_le_of_lt h1]
  · have : ¬ j + 1 ≤ n := by omega
    simp [h1, this]

theorem gu_lt (GR j : Nat) : gu GR j < 2 ^ 22 := by
  change (fget GR j 22) &&& _ < _
  exact Nat.and_lt_two_pow _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide))

@[expose] def pb : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, y => pb n y ^^ y.testBit n

theorem pb_congr {y z : Nat} : ∀ d, (∀ i < d, y.testBit i = z.testBit i) → pb d y = pb d z
  | 0, _ => rfl
  | d + 1, h => by
    change (pb d y ^^ y.testBit d) = (pb d z ^^ z.testBit d)
    rw [h d (Nat.lt_succ_self d), pb_congr d fun i hi => h i (Nat.lt_succ_of_lt hi)]

private def sh (k y : Nat) : Nat := y ^^^ (y >>> k)

private theorem sh_xor (k a b : Nat) : sh k (a ^^^ b) = sh k a ^^^ sh k b := by
  unfold sh
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]
  generalize a.testBit i = x
  generalize b.testBit i = y
  generalize a.testBit (k + i) = z
  generalize b.testBit (k + i) = u
  cases x <;> cases y <;> cases z <;> cases u <;> rfl

theorem par_xor (a b : Nat) : par (a ^^^ b) = par a ^^^ par b := by
  have e : ∀ x, par x = sh 1 (sh 2 (sh 4 (sh 8 (sh 16 (x &&& 4294967295))))) &&& 1 := fun _ => rfl
  rw [e, e, e, Nat.and_xor_distrib_right, sh_xor, sh_xor, sh_xor, sh_xor, sh_xor,
    Nat.and_xor_distrib_right]

theorem par_zero : par 0 = 0 := rfl

theorem par_pow (d : Nat) (hd : d < 22) : par (2 ^ d) = 1 := by
  exact (by decide : ∀ d, d < 22 → par (2 ^ d) = 1) d hd

theorem split_top (y d : Nat) (hy : y < 2 ^ (d + 1)) :
    y = (y &&& (2 ^ d - 1)) ^^^ (if y.testBit d then 2 ^ d else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < d
  · have : ¬ d = i := by omega
    cases y.testBit d <;> simp [hi, this]
  · by_cases h2 : d = i
    · subst h2
      cases h : y.testBit d <;> simp [h]
    · have hi' : d + 1 ≤ i := by omega
      have : y.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hi'))
      cases y.testBit d <;> simp [hi, h2, this]

theorem par_pb : ∀ d, d ≤ 22 → ∀ y, y < 2 ^ d → par y = if pb d y then 1 else 0
  | 0, _, y, hy => by
    have : y = 0 := by simpa using hy
    subst this
    rfl
  | d + 1, hd, y, hy => by
    have hy' : y &&& (2 ^ d - 1) < 2 ^ d :=
      Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := d); omega)
    have ih := par_pb d (by omega) _ hy'
    have hs := split_top y d hy
    have hpb : pb d (y &&& (2 ^ d - 1)) = pb d y := by
      apply pb_congr
      intro i hi
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
      simp [hi]
    rw [hpb] at ih
    have hp : par y = par (y &&& (2 ^ d - 1)) ^^^ (if y.testBit d then 1 else 0) := by
      have h := congrArg par hs
      rw [par_xor] at h
      rw [h]
      cases y.testBit d
      · simp [par_zero]
      · simp [par_pow d (by omega)]
    rw [hp, ih]
    change _ = if (pb d y ^^ y.testBit d) then 1 else 0
    cases pb d y <;> cases y.testBit d <;> rfl

theorem cAtN_eq (GR m : Nat) (u : Nat) (hm : m < 22) :
    ∀ n, n ≤ 22 → cAtN (fget GR m 22) u m n = pb n (u &&& gu GR m)
  | 0, _ => rfl
  | n + 1, hn => by
    change (cAtN (fget GR m 22) u m n ^^ (decide (m < n) && u.testBit n && (fget GR m 22).testBit n))
      = (pb n (u &&& gu GR m) ^^ (u &&& gu GR m).testBit n)
    rw [cAtN_eq GR m u hm n (by omega), Nat.testBit_and, testBit_gu GR m n hm]
    have : decide (n < 22) = true := by simpa using (by omega : n < 22)
    rw [this]
    cases u.testBit n <;> cases (fget GR m 22).testBit n <;> cases decide (m < n) <;> rfl

theorem par_gu (G : Array Nat) (GR m a : Nat) (hm : m < 22) (hG : G.getD m 0 = fget GR m 22) :
    par (a &&& gu GR m) = if cAt G a m then 1 else 0 := by
  have hlt : a &&& gu GR m < 2 ^ 22 := Nat.and_lt_two_pow _ (gu_lt GR m)
  rw [par_pb 22 (Nat.le_refl _) _ hlt]
  have : cAt G a m = pb 22 (a &&& gu GR m) := by
    unfold cAt
    rw [hG]
    exact cAtN_eq GR m a hm 22 (Nat.le_refl _)
  rw [this]

@[expose] noncomputable def MBx (GR b : Nat) : Nat := xorN 22 fun j => if b.testBit j then gu GR j else 0

theorem corrN_eq (G : Array Nat) (a b : Nat) : ∀ m,
    (if corrN G a b m then 1 else 0 : Nat) =
      xorN m (fun j => if b.testBit j then (if cAt G a j then 1 else 0) else 0)
  | 0 => rfl
  | m + 1 => by
    rw [xorN_succ]
    change (if (if b.testBit m then corrN G a b m ^^ cAt G a m else corrN G a b m) then 1 else 0 : Nat) = _
    rw [← corrN_eq G a b m]
    cases b.testBit m <;> cases corrN G a b m <;> cases cAt G a m <;> rfl

theorem par_MBx (G : Array Nat) (GR a b : Nat) (hG : ∀ j < 22, G.getD j 0 = fget GR j 22) :
    par (a &&& MBx GR b) = if corr G a b then 1 else 0 := by
  unfold corr
  rw [corrN_eq]
  unfold MBx
  rw [xorN_lin (h := fun x => a &&& x) (fun x y => Nat.and_xor_distrib_left) 22,
    xorN_lin (h := par) par_xor]
  refine xorN_congr fun j hj => ?_
  cases hb : b.testBit j
  · simp [par_zero]
  · simp [par_gu G GR j a hj (hG j hj)]

theorem mbByte_lt (GR k x : Nat) : mbByte GR k x < 2 ^ 22 := by
  unfold mbByte
  refine xorN_lt fun t _ => ?_
  rw [brec_eq]
  split
  · exact gu_lt _ _
  · exact Nat.two_pow_pos 22

theorem mbByte_eq (GR k x : Nat) :
    mbByte GR k x = xorN 8 fun t =>
      if x.testBit t && decide (8 * k + t < 22) then gu GR (8 * k + t) else 0 := by
  unfold mbByte
  refine xorN_congr fun t _ => ?_
  rw [brec_eq, andB_eq, bit_eq, blt_eq]
  rfl

theorem fget_tbOf (GR i k x : Nat) (hk : k < 3) (hx : x < 256) (hi : i = 256 * k + x) :
    fget (tbOf GR) i 22 = mbByte GR k x := by
  have e : tbOf GR = orN 768 fun t =>
      mbByte GR (t >>> 8) (t &&& 255) <<< (22 * t) := rfl
  have := fget_pack (w := 22) (n := 768) (F := fun t => mbByte GR (t >>> 8) (t &&& 255))
    (fun j _ => mbByte_lt _ _ _) (i := i) (by omega)
  rw [e, this]
  have h1 : i >>> 8 = k := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : i &&& 255 = x := by
    rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [h1, h2]

theorem byte_tb (b s t : Nat) (ht : t < 8) : ((b >>> s) &&& 255).testBit t = b.testBit (s + t) := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight]
  simp [ht]

theorem and255_lt (x : Nat) : x &&& 255 < 256 :=
  Nat.and_lt_two_pow (n := 8) x (by decide)

theorem mb_tbOf (GR b : Nat) : mb (tbOf GR) b = MBx GR b := by
  let f : Nat → Nat := fun j => if b.testBit j && decide (j < 22) then gu GR j else 0
  have x0 : b &&& 255 < 256 := and255_lt b
  have x1 : (b >>> 8) &&& 255 < 256 := and255_lt _
  have x2 : (b >>> 16) &&& 255 < 256 := and255_lt _
  have e0 : fget (tbOf GR) (b &&& 255) 22 = xorN 8 fun t => f t := by
    rw [fget_tbOf GR _ 0 _ (by omega) x0 (by omega), mbByte_eq]
    refine xorN_congr fun t ht => ?_
    have := byte_tb b 0 t ht
    rw [Nat.shiftRight_zero] at this
    simp only [this, f, Nat.mul_zero, Nat.zero_add]
  have e1 : fget (tbOf GR) (256 + ((b >>> 8) &&& 255)) 22 = xorN 8 fun t => f (8 + t) := by
    rw [fget_tbOf GR _ 1 _ (by omega) x1 (by omega), mbByte_eq]
    refine xorN_congr fun t ht => ?_
    simp only [byte_tb b 8 t ht, f, Nat.mul_one]
  have e2 : fget (tbOf GR) (512 + ((b >>> 16) &&& 255)) 22 = xorN 8 fun t => f (16 + t) := by
    rw [fget_tbOf GR _ 2 _ (by omega) x2 (by omega), mbByte_eq]
    refine xorN_congr fun t ht => ?_
    simp only [byte_tb b 16 t ht, f, show 8 * 2 = 16 from rfl]
  have e3 : mb (tbOf GR) b = xorN 24 f := by
    change Nat.xor (fget (tbOf GR) (b &&& 255) 22) (Nat.xor (fget (tbOf GR)
      (256 + ((b >>> 8) &&& 255)) 22) (fget (tbOf GR) (512 + ((b >>> 16) &&& 255)) 22)) = _
    rw [e0, e1, e2, show (24 : Nat) = 8 + 16 from rfl, xorN_add, show (16 : Nat) = 8 + 8 from rfl,
      xorN_add]
    simp only [Nat.add_assoc]
    rfl
  rw [e3, show (24 : Nat) = 22 + 2 from rfl, xorN_add]
  have z : xorN 2 (fun i => f (22 + i)) = 0 := by
    rw [xorN_congr (g := fun _ => 0) (fun i _ => by
      have : ¬ 22 + i < 22 := by omega
      simp [f, this]), xorN_zeros]
  rw [z, Nat.xor_zero]
  unfold MBx
  refine xorN_congr fun j hj => ?_
  simp [f, hj]

theorem qmul_lt (G : Array Nat) (a b : Nat) : qmul G a b < 2 ^ 23 := by
  unfold qmul
  refine Nat.or_lt_two_pow ?_ ?_
  · exact Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos 22)) (Nat.pow_lt_pow_right (by omega) (by omega))
  · split
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
    · exact Nat.two_pow_pos 23

theorem shr22 (a : Nat) (ha : a < 2 ^ 23) : a >>> 22 = if a.testBit 22 then 1 else 0 := by
  have h : a / 2 ^ 22 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 22)]
    have : (2 : Nat) ^ 23 = 2 * 2 ^ 22 := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  rw [Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases (by omega : a / 2 ^ 22 = 0 ∨ a / 2 ^ 22 = 1) with h0 | h0 <;> simp [h0]

theorem qmulK_eq {GR : Nat} {gL : List Nat} (hg : gL.length = 22) (hb : bindL GR 22 gL = true)
    {a b : Nat} (ha : a < 2 ^ 23) (hb' : b < 2 ^ 23) :
    qmulK (tbOf GR) a b = qmul gL.toArray a b := by
  have hG : ∀ j < 22, gL.toArray.getD j 0 = fget GR j 22 := fun j hj =>
    bindL_getD hb (by omega)
  have hp := par_MBx gL.toArray GR a b hG
  have key : qmulK (tbOf GR) a b = ((a ^^^ b) &&& M22) |||
      ((((a >>> 22) ^^^ (b >>> 22)) ^^^ par (a &&& mb (tbOf GR) b)) &&& 1) <<< 22 := rfl
  rw [key, mb_tbOf, hp, shr22 a ha, shr22 b hb']
  unfold qmul
  have hm : (a ^^^ b) &&& M22 = (a ^^^ b) % 2 ^ 22 := by
    rw [show M22 = 2 ^ 22 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [hm]
  generalize a.testBit 22 = sa
  generalize b.testBit 22 = sb
  generalize corr gL.toArray a b = c
  cases sa <;> cases sb <;> cases c <;> simp

@[expose] noncomputable def autApplyKN (TB A n : Nat) : Nat → Nat :=
  fun m => Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (Nat.land (Nat.shiftRight n (nat_lit 22)) (nat_lit 1)) (nat_lit 22))
    (fun m ih => strictN ih fun acc => nIf(bit n m, qmulK TB acc (img A m), acc)) m

theorem autApplyN_lt (G A : Array Nat) (n : Nat) : ∀ m, autApplyN G A n m < 2 ^ 23
  | 0 => by
    unfold autApplyN
    split
    · exact Nat.pow_lt_pow_right (by omega) (by omega)
    · exact Nat.two_pow_pos 23
  | m + 1 => by
    unfold autApplyN
    split
    · exact qmul_lt _ _ _
    · exact autApplyN_lt G A n m

theorem autApply_lt (G A : Array Nat) (n : Nat) : autApply G A n < 2 ^ 23 :=
  autApplyN_lt G A n 22

theorem autApplyKN_eq {GR A : Nat} {gL a : List Nat} (hg : gL.length = 22) (ha : a.length = 22)
    (hb : bindL GR 22 gL = true) (hA : bindL A 23 a = true) {n : Nat} (hn : n < 2 ^ 23) :
    ∀ m, m ≤ 22 → autApplyKN (tbOf GR) A n m = autApplyN gL.toArray a.toArray n m
  | 0, _ => by
    change Nat.shiftLeft (Nat.land (Nat.shiftRight n 22) 1) 22 = autApplyN gL.toArray a.toArray n 0
    unfold autApplyN
    have h1 : n >>> 22 = if n.testBit 22 then 1 else 0 := shr22 n hn
    change ((n >>> 22) &&& 1) <<< 22 = _
    rw [h1]
    cases n.testBit 22 <;> simp
  | m + 1, hm => by
    have ih := autApplyKN_eq hg ha hb hA hn m (by omega)
    change strictN (autApplyKN (tbOf GR) A n m) (fun acc =>
      nIf(bit n m, qmulK (tbOf GR) acc (img A m), acc)) = _
    rw [strictN_eq, ih]
    have e : autApplyN gL.toArray a.toArray n (m + 1) = if n.testBit m then
        qmul gL.toArray (autApplyN gL.toArray a.toArray n m) (a.toArray.getD m 0)
        else autApplyN gL.toArray a.toArray n m := rfl
    rw [e, brec_eq, bit_eq]
    split
    · have hi : img A m = a.toArray.getD m 0 := (bindL_getD hA (by omega)).symm
      rw [hi]
      exact qmulK_eq hg hb (autApplyN_lt _ _ _ _) (bindL_lt hA (by omega))
    · rfl

end Aux

theorem autApplyK_eq {GR A : Nat} {gL a : List Nat} (hg : gL.length = 22) (ha : a.length = 22)
    (hb : bindL GR 22 gL = true) (hA : bindL A 23 a = true) {n : Nat} (hn : n < 2 ^ 23) :
    autApplyK (tbOf GR) A n = autApply gL.toArray a.toArray n :=
  Aux.autApplyKN_eq hg ha hb hA hn 22 (Nat.le_refl _)

theorem bindsL_spec {GR A6 A8 Q1 Q2 : Nat} {gL a6 a8 q1 q2 : List Nat}
    (h : bindsL GR gL A6 a6 A8 a8 Q1 q1 Q2 q2 = true) :
    (gL.length = 22 ∧ bindL GR 22 gL = true) ∧ (a6.length = 22 ∧ bindL A6 23 a6 = true) ∧
      (a8.length = 22 ∧ bindL A8 23 a8 = true) ∧ (q1.length = 22 ∧ bindL Q1 22 q1 = true) ∧
      (q2.length = 22 ∧ bindL Q2 22 q2 = true) := by
  unfold bindsL at h
  simp only [Aux.andB_eq, Bool.and_eq_true, Aux.lenL_eq] at h
  simp only [Nat.beq_eq] at h
  exact h

theorem qmulK_eq {GR : Nat} {gL : List Nat} (hg : gL.length = 22) (hb : bindL GR 22 gL = true)
    {a b : Nat} (ha : a < 2 ^ 23) (hb' : b < 2 ^ 23) :
    qmulK (tbOf GR) a b = qmul gL.toArray a b :=
  Aux.qmulK_eq hg hb ha hb'

theorem qmul_lt {G : Array Nat} (a b : Nat) : qmul G a b < 2 ^ 23 := Aux.qmul_lt G a b

theorem autApply_lt {G A : Array Nat} (n : Nat) : autApply G A n < 2 ^ 23 := Aux.autApply_lt G A n

namespace Aux

theorem bindLG_intro (P w : Nat) : ∀ (l : List Nat) (k : Nat),
    (∀ i (hi : i < l.length), l[i] < 2 ^ w ∧ l[i] = fget P (k + i) w) → bindLG P w l k = true
  | [], _, _ => rfl
  | x :: t, k, h => by
    have h0 := h 0 (by simp)
    have h1 : bindLG P w t (Nat.succ k) = true := by
      refine bindLG_intro P w t (Nat.succ k) fun i hi => ?_
      have := h (i + 1) (by simpa using hi)
      rw [Nat.succ_add, ← Nat.add_succ] at *
      simpa [Nat.add_assoc, Nat.add_comm 1 i, Nat.succ_add] using this
    change andB (Nat.blt x (pw2 w)) (andB (Nat.beq x (fget P k w)) (bindLG P w t (Nat.succ k))) = true
    rw [andB_eq, andB_eq, h1, blt_eq, pw2_eq]
    have e : x = fget P k w := by simpa using h0.2
    have : x < 2 ^ w := by simpa using h0.1
    have hb : Nat.beq x (fget P k w) = true := Nat.beq_eq.mpr e
    rw [hb, decide_eq_true this]
    rfl

theorem bindL_intro {P w : Nat} {l : List Nat}
    (h : ∀ i (hi : i < l.length), l[i] < 2 ^ w ∧ l[i] = fget P i w) : bindL P w l = true :=
  bindLG_intro P w l 0 (by simpa using h)

end Aux

@[expose] def PkAut (P : Nat) (X : Array Nat) : Prop := X.size = 22 ∧ bindL P 23 X.toList = true

namespace Aux

theorem img_eq (A i : Nat) : img A i = fget A i 23 := rfl

theorem Bd_pack {F : Nat → Nat} (hF : ∀ i < 22, F i < 2 ^ 23) :
    PkAut (orN 22 fun i => F i <<< (23 * i)) ((List.range 22).map F).toArray := by
  refine ⟨by simp, ?_⟩
  rw [List.toList_toArray]
  refine bindL_intro fun i hi => ?_
  have hi' : i < 22 := by simpa using hi
  simp only [List.getElem_map, List.getElem_range]
  exact ⟨hF i hi', (fget_pack hF hi').symm⟩

theorem Bd_inj {P : Nat} {X Y : Array Nat} (hX : PkAut P X) (hY : PkAut P Y) : X = Y := by
  apply Array.ext
  · rw [hX.1, hY.1]
  · intro i h1 h2
    have a1 := (bindL_get hX.2 (i := i) (by simpa using h1)).2
    have a2 := (bindL_get hY.2 (i := i) (by simpa using h2)).2
    simp only [Array.getElem_toList] at a1 a2
    rw [a1, a2]

theorem Bd_getD {P : Nat} {X : Array Nat} (hX : PkAut P X) {i : Nat} (hi : i < 22) :
    X.getD i 0 = fget P i 23 := by
  have hs := hX.1
  have := (bindL_get hX.2 (i := i) (by simpa [hX.1] using hi)).2
  simpa [Array.getD, show i < X.size by omega] using this

theorem Bd_ID23 : PkAut ID23 (id23 ()) := by
  have h := Bd_pack (F := fun i => pw2 i) (fun i hi => by
    rw [pw2_eq]
    exact Nat.pow_lt_pow_right (by omega) (by omega))
  have e : ((List.range 22).map fun i => pw2 i).toArray = id23 () := by
    simp only [id23, pw2_eq]
  rw [e] at h
  exact h

theorem orN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) : orN n f = orN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (f n ||| orN n f) = (g n ||| orN n g)
    rw [h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

@[expose] noncomputable def wordRec (TB G0 G1 GI : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A)
    (fun l _ ih A => strictN (autCompK TB A
      (nIf(Nat.beq l (nat_lit 0), G0, nIf(Nat.beq l (nat_lit 1), G1, GI)))) ih) w

theorem wordRec_cons (TB G0 G1 GI l : Nat) (t : List Nat) (A : Nat) :
    wordRec TB G0 G1 GI (l :: t) A = wordRec TB G0 G1 GI t (autCompK TB A
      (if l = 0 then G0 else if l = 1 then G1 else GI)) := by
  change strictN _ (wordRec TB G0 G1 GI t) = _
  rw [strictN_eq, brec_eq, brec_eq]
  simp only [Nat.beq_eq]

theorem shr_and_one (x t : Nat) : (x >>> t) &&& 1 = if x.testBit t then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ t) with h | h <;> simp [h]

end Aux

theorem Bd_ID23 : PkAut ID23 (id23 ()) := Aux.Bd_ID23

theorem Bd_inj {P : Nat} {X Y : Array Nat} (hX : PkAut P X) (hY : PkAut P Y) : X = Y := Aux.Bd_inj hX hY

section Packed

variable {GR : Nat} {gL : List Nat} (hg : gL.length = 22) (hb : bindL GR 22 gL = true)
include hg hb

theorem Bd_autApplyK {A : Nat} {X : Array Nat} (hX : PkAut A X) {n : Nat} (hn : n < 2 ^ 23) :
    autApplyK (tbOf GR) A n = autApply gL.toArray X n := by
  have := autApplyK_eq (a := X.toList) hg (by simpa using hX.1) hb hX.2 hn
  simpa using this

theorem Bd_autCompK {A B : Nat} {X Y : Array Nat} (hX : PkAut A X) (hY : PkAut B Y) :
    PkAut (autCompK (tbOf GR) A B) (autComp gL.toArray X Y) := by
  have e1 : autCompK (tbOf GR) A B =
      orN 22 fun i => autApplyK (tbOf GR) B (img A i) <<< (23 * i) := by
    unfold autCompK
    simp only [Aux.strictN_eq]
    rfl
  have hl : ∀ i < 22, autApplyK (tbOf GR) B (img A i) = autApply gL.toArray Y (X.getD i 0) := by
    intro i hi
    have := Aux.Bd_getD hX hi
    rw [Aux.img_eq, Bd_autApplyK hg hb hY (Aux.fget_lt _ _ _), this]
  have e2 : autComp gL.toArray X Y =
      ((List.range 22).map fun i => autApplyK (tbOf GR) B (img A i)).toArray := by
    apply Array.ext
    · simp [autComp, hX.1]
    · intro i h1 h2
      have hi : i < 22 := by simpa [autComp, hX.1] using h1
      have hX1 := hX.1
      simp only [autComp, Array.getElem_map, List.getElem_toArray, List.getElem_map,
        List.getElem_range]
      rw [hl i hi]
      simp [Array.getD, show i < X.size by omega]
  rw [e1, e2]
  refine Aux.Bd_pack (F := fun i => autApplyK (tbOf GR) B (img A i)) fun i _ => ?_
  show autApplyK (tbOf GR) B (img A i) < 2 ^ 23
  rw [Aux.img_eq, Bd_autApplyK hg hb hY (Aux.fget_lt _ _ _)]
  exact autApply_lt _

theorem Bd_autPowK {A : Nat} {X : Array Nat} (hX : PkAut A X) (k : Nat) :
    PkAut (autPowK (tbOf GR) A k) (autPow gL.toArray X k) := by
  induction k with
  | zero => exact Aux.Bd_ID23
  | succ k ih => exact Bd_autCompK hg hb ih hX

theorem qinvK_eq {d : Nat} (hd : d < 2 ^ 23) :
    qinvK (tbOf GR) d = qmul gL.toArray (qmul gL.toArray d d) d := by
  unfold qinvK
  rw [qmulK_eq hg hb hd hd, qmulK_eq hg hb (qmul_lt _ _) hd]

theorem Bd_innerK {d : Nat} (hd : d < 2 ^ 23) :
    PkAut (innerK (tbOf GR) d) ((List.range 22).map fun i =>
      qmul gL.toArray (qmul gL.toArray (qmul gL.toArray (qmul gL.toArray d d) d) (2 ^ i)) d).toArray := by
  have hp : ∀ i < 22, (2 : Nat) ^ i < 2 ^ 23 := fun i hi => Nat.pow_lt_pow_right (by omega) (by omega)
  have e : innerK (tbOf GR) d = orN 22 fun i => (qmul gL.toArray (qmul gL.toArray
      (qmul gL.toArray (qmul gL.toArray d d) d) (2 ^ i)) d) <<< (23 * i) := by
    unfold innerK
    refine Aux.orN_congr fun i hi => ?_
    change qmulK (tbOf GR) (qmulK (tbOf GR) (qinvK (tbOf GR) d) (pw2 i)) d <<< (23 * i) = _
    rw [qinvK_eq hg hb hd, Aux.pw2_eq, qmulK_eq hg hb (qmul_lt _ _) (hp i hi),
      qmulK_eq hg hb (qmul_lt _ _) hd]
  rw [e]
  exact Aux.Bd_pack fun i _ => qmul_lt _ _

theorem Bd_sgnImg {Q s : Nat} {q : List Nat} (hq : q.length = 22) (hQ : bindL Q 22 q = true) :
    PkAut (sgnImg Q s) ((List.range 22).map fun i => signedImg q s i).toArray := by
  have hl : ∀ i < 22, signedImg q s i = fget Q i 22 ||| (((s >>> i) &&& 1) <<< 22) := by
    intro i hi
    have h1 : q.getD i 0 = fget Q i 22 := by
      have := Aux.bindL_getD hQ (i := i) (by omega)
      have hi' : i < q.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      simpa [Array.getD, hi'] using this
    unfold signedImg
    rw [h1, Aux.shr_and_one]
    cases s.testBit i <;> simp
  have e : sgnImg Q s = orN 22 fun i => (signedImg q s i) <<< (23 * i) := by
    unfold sgnImg
    refine Aux.orN_congr fun i hi => ?_
    rw [hl i hi]
    rfl
  rw [e]
  refine Aux.Bd_pack fun i hi => ?_
  rw [hl i hi]
  have h22 : (2 : Nat) ^ 22 < 2 ^ 23 := Nat.pow_lt_pow_right (by omega) (by omega)
  refine Nat.or_lt_two_pow (Nat.lt_trans (Aux.fget_lt Q i 22) h22) ?_
  rw [Aux.shr_and_one]
  cases s.testBit i
  · exact Nat.two_pow_pos 23
  · exact h22

theorem Bd_wordAutK {G0 G1 GI : Nat} {g0 g1 gi : Array Nat} (h0 : PkAut G0 g0) (h1 : PkAut G1 g1)
    (hI : PkAut GI gi) (w : List Nat) :
    PkAut (wordAutK (tbOf GR) G0 G1 GI w)
      (w.foldl (fun X l => autComp gL.toArray X (if l = 0 then g0 else if l = 1 then g1 else gi))
        (id23 ())) := by
  have key : ∀ (w : List Nat) (A : Nat) (X : Array Nat), PkAut A X →
      PkAut (Aux.wordRec (tbOf GR) G0 G1 GI w A)
        (w.foldl (fun X l => autComp gL.toArray X (if l = 0 then g0 else if l = 1 then g1 else gi)) X) := by
    intro w
    induction w with
    | nil => intro A X hX; exact hX
    | cons l t ih =>
      intro A X hX
      rw [Aux.wordRec_cons, List.foldl_cons]
      refine ih _ _ (Bd_autCompK hg hb hX ?_)
      by_cases a : l = 0 <;> by_cases b : l = 1 <;> simp [a, b, h0, h1, hI]
  exact key w ID23 (id23 ()) Aux.Bd_ID23

end Packed

end CFSG.KC.CTIBq

end
