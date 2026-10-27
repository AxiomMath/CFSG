module

public import Certificates.Data.Kernel.O8.SplitK

public section

namespace CFSG.KC.O8Split

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.NSplit
  CFSG.EvenSmallLie.UnitarySix.YamadaPar Finset

private theorem testBit_fld (w x k t : ℕ) :
    (fld w x k).testBit t = (decide (t < w) && x.testBit (w * k + t)) :=
  testBit_blkN w x k t

private theorem fld_lt (w x k : ℕ) : fld w x k < 2 ^ w := Nat.mod_lt _ (by positivity)

private theorem fld_xor (w a b k : ℕ) : fld w (a ^^^ b) k = fld w a k ^^^ fld w b k := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [testBit_fld, Nat.testBit_xor]
  cases decide (t < w) <;> simp

private theorem fld_zero (w k : ℕ) : fld w 0 k = 0 := by simp [fld]

private theorem blkN_xor (n a b k : ℕ) : blkN n (a ^^^ b) k = blkN n a k ^^^ blkN n b k :=
  fld_xor n a b k

private theorem testBit_lt_pow {v w t : ℕ} (hv : v < 2 ^ w) (ht : w ≤ t) : v.testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) ht))

private theorem packN_eq (w n : ℕ) (f : ℕ → ℕ) : packN w n f = foldOr n w f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldOr_succ, ← ih]
    rfl

private theorem foldOr_congr {k n : ℕ} {f f' : ℕ → ℕ} (h : ∀ g < k, f g = f' g) :
    foldOr k n f = foldOr k n f' := by
  induction k with
  | zero => rfl
  | succ k ih => rw [foldOr_succ, foldOr_succ, ih (fun g hg => h g (by omega)), h k (by omega)]

private theorem lt_mul_of_lt {w c n t : ℕ} (hc : c < n) (ht : t < w) : w * c + t < w * n := by
  have : w * (c + 1) ≤ w * n := Nat.mul_le_mul_left w hc
  rw [Nat.mul_succ] at this
  omega

private theorem fld_foldOr {w : ℕ} (hw : 0 < w) {n : ℕ} (f : ℕ → ℕ) (hf : ∀ g < n, f g < 2 ^ w)
    {c : ℕ} (hc : c < n) : fld w (foldOr n w f) c = f c := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_fld, testBit_foldOr hw f n hf]
  by_cases ht : t < w
  · have h2 : (w * c + t) / w = c := by
      rw [Nat.mul_add_div hw, Nat.div_eq_of_lt ht, Nat.add_zero]
    have h3 : (w * c + t) % w = t := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
    simp [ht, lt_mul_of_lt hc ht, h2, h3]
  · simp only [ht, decide_false, Bool.false_and]
    exact (testBit_lt_pow (hf c hc) (by omega)).symm

private theorem foldOr_xor {k n : ℕ} (hn : 0 < n) {f f' : ℕ → ℕ} (hf : ∀ g < k, f g < 2 ^ n)
    (hf' : ∀ g < k, f' g < 2 ^ n) :
    foldOr k n (fun g => f g ^^^ f' g) = foldOr k n f ^^^ foldOr k n f' := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor, testBit_foldOr hn _ k (fun g hg => Nat.xor_lt_two_pow (hf g hg) (hf' g hg)),
    testBit_foldOr hn f k hf, testBit_foldOr hn f' k hf', Nat.testBit_xor]
  cases decide (t < n * k) <;> simp

private theorem fld_shift {w N x : ℕ} (hx : x < 2 ^ (w * N)) (i i0 : ℕ) {c : ℕ} (hc : c < N) :
    fld w (x <<< (w * N * i)) (N * i0 + c) = if i = i0 then fld w x c else 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_fld]
  by_cases ht : t < w
  · have hpos : w * (N * i0 + c) + t = w * N * i0 + (w * c + t) := by ring
    have hlt : w * c + t < w * N := lt_mul_of_lt hc ht
    rw [hpos, Nat.testBit_shiftLeft]
    split_ifs with hi
    · subst hi
      rw [testBit_fld]
      simp [ht]
    · rw [Nat.zero_testBit]
      simp only [ht, decide_true, Bool.true_and]
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · have : w * N * (i + 1) ≤ w * N * i0 := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        have hge : w * N ≤ w * N * i0 + (w * c + t) - w * N * i := by omega
        rw [testBit_lt_pow hx hge, Bool.and_false]
      · have : w * N * (i0 + 1) ≤ w * N * i := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        have : ¬ (w * N * i0 + (w * c + t) ≥ w * N * i) := by omega
        simp [this]
  · simp only [ht, decide_false, Bool.false_and]
    split_ifs <;> simp [testBit_fld, ht]

private theorem bz_xorFold_range (k : ℕ) (f : ℕ → Bool) :
    bz (xorFold k f) = ∑ j ∈ range k, bz (f j) := by
  rw [bz_xorFold, Fin.sum_univ_eq_sum_range (fun j => bz (f j))]

private theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → M) :
    ∑ r ∈ range (a * b), f r = ∑ j ∈ range a, ∑ c ∈ range b, f (j * b + c) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

private theorem bz_add_self (q : Bool) : bz q + bz q = 0 := by cases q <;> decide

private theorem bz_ite (c : Bool) (u k : ℕ) :
    bz ((if c = true then u else 0).testBit k) = bz c * bz (u.testBit k) := by
  cases c <;> simp

private theorem divmod_aux {n j c : ℕ} (hc : c < n) : (j * n + c) / n = j ∧ (j * n + c) % n = c := by
  have hn : 0 < n := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

private theorem lt_block {n j c N : ℕ} (hj : j < N) (hc : c < n) : j * n + c < N * n := by
  have : (j + 1) * n ≤ N * n := Nat.mul_le_mul_right n hj
  rw [Nat.succ_mul] at this
  omega

private theorem testBit_xorN (n : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    (xorN n f).testBit k = xorFold n fun i => (f i).testBit k := by
  induction n with
  | zero => simp [xorN, xorFold]
  | succ n ih => simp only [xorN, xorFold_succ, Nat.testBit_xor, ih]

private theorem bz_xorN (n : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    bz ((xorN n f).testBit k) = ∑ i ∈ range n, bz ((f i).testBit k) := by
  rw [testBit_xorN, bz_xorFold_range]

private theorem xorN_lt {n w : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) : xorN n f < 2 ^ w := by
  induction n with
  | zero => exact Nat.two_pow_pos w
  | succ n ih => exact Nat.xor_lt_two_pow (ih fun i hi => hf i (by omega)) (hf n (by omega))

private theorem xorN_congr {n : ℕ} {f f' : ℕ → ℕ} (h : ∀ i < n, f i = f' i) :
    xorN n f = xorN n f' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change xorN n f ^^^ f n = xorN n f' ^^^ f' n
    rw [ih fun i hi => h i (by omega), h n (by omega)]

private theorem xorN_mask_xor (n : ℕ) (a : ℕ → ℕ) (x y : ℕ) :
    xorN n (fun b => if (x ^^^ y).testBit b then a b else 0) =
      xorN n (fun b => if x.testBit b then a b else 0) ^^^
        xorN n (fun b => if y.testBit b then a b else 0) := by
  apply Nat.eq_of_testBit_eq
  intro t
  apply bz_injective
  rw [Nat.testBit_xor, bz_xor, bz_xorN, bz_xorN, bz_xorN, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> simp [bz_add_self]

private theorem map_xorN {K : ℕ} {φ : ℕ → ℕ} (h0 : φ 0 = 0)
    (hadd : ∀ a b, a < 2 ^ K → b < 2 ^ K → φ (a ^^^ b) = φ a ^^^ φ b) {n : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i < n, f i < 2 ^ K) : φ (xorN n f) = xorN n fun i => φ (f i) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    change φ (xorN n f ^^^ f n) = xorN n (fun i => φ (f i)) ^^^ φ (f n)
    rw [hadd _ _ (xorN_lt fun i hi => hf i (by omega)) (hf n (by omega)),
      ih fun i hi => hf i (by omega)]

private theorem ite_map {φ : ℕ → ℕ} (h0 : φ 0 = 0) (c : Bool) (u : ℕ) :
    φ (if c = true then u else 0) = if c = true then φ u else 0 := by
  cases c <;> simp [h0]

private theorem xorN_bits {v : ℕ} (hv : v < 2 ^ 7) :
    xorN 7 (fun b => if v.testBit b then 2 ^ b else 0) = v := by
  apply Nat.eq_of_testBit_eq
  intro t
  apply bz_injective
  rw [bz_xorN]
  simp only [bz_ite, Nat.testBit_two_pow]
  by_cases ht : t < 7
  · rw [sum_eq_single t]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (mem_range.2 ht) h
  · rw [sum_eq_zero, testBit_lt_pow hv (by omega)]
    · rfl
    · intro b hb
      have : b ≠ t := by have := mem_range.1 hb; omega
      simp [this]

private theorem allN_eq_true {n : ℕ} {p : ℕ → Bool} : allN n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    simp only [allN, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · exact h ▸ h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem getD_ofFn' {n : ℕ} (f : Fin n → ℕ) {r : ℕ} (hr : r < n) :
    (Array.ofFn f).getD r 0 = f ⟨r, hr⟩ := by
  simp [Array.getD_eq_getD_getElem?, hr]

private def permOK (ε : Eps) : Bool :=
  (List.range 7).all fun i => (List.range (mOf ε)).all fun g =>
    decide (permIdx ε i g < mOf ε) && permIdx ε i (permIdx ε i g) == g

private theorem permOK_true (ε : Eps) : permOK ε = true := by cases ε <;> decide +kernel

private theorem perm_facts (ε : Eps) {i g : ℕ} (hi : i < 7) (hg : g < mOf ε) :
    permIdx ε i g < mOf ε ∧ permIdx ε i (permIdx ε i g) = g := by
  have h := permOK_true ε
  simp only [permOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h i hi g hg

private def actLinOK (ε : Eps) : Bool :=
  (List.range 7).all fun i => (List.range 128).all fun x =>
    decide (actECode ε i x < 128) &&
      actECode ε i x == xorN 7 fun b => if x.testBit b then actECode ε i (2 ^ b) else 0

private theorem actLinOK_true (ε : Eps) : actLinOK ε = true := by cases ε <;> decide +kernel

private theorem actE_facts (ε : Eps) {i x : ℕ} (hi : i < 7) (hx : x < 2 ^ 7) :
    actECode ε i x < 2 ^ 7 ∧
      actECode ε i x = xorN 7 fun b => if x.testBit b then actECode ε i (2 ^ b) else 0 := by
  have h := actLinOK_true ε
  simp only [actLinOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h i hi x (by simpa using hx)

private theorem actE_xor (ε : Eps) {i x y : ℕ} (hi : i < 7) (hx : x < 2 ^ 7) (hy : y < 2 ^ 7) :
    actECode ε i (x ^^^ y) = actECode ε i x ^^^ actECode ε i y := by
  rw [(actE_facts ε hi hx).2, (actE_facts ε hi hy).2,
    (actE_facts ε hi (Nat.xor_lt_two_pow hx hy)).2, xorN_mask_xor]

private theorem actE_zero (ε : Eps) {i : ℕ} (hi : i < 7) : actECode ε i 0 = 0 := by
  have := actE_xor ε hi (x := 0) (y := 0) (by norm_num) (by norm_num)
  simpa using this

private theorem relWords_lt (j : ℕ) : ∀ i ∈ relWords.getD j [], i < 7 := by
  intro i hi
  have hall : ∀ l ∈ relWords, ∀ i ∈ l, i < 7 := by decide
  rw [List.getD_eq_getElem?_getD] at hi
  rcases h : relWords[j]? with _ | l
  · simp [h] at hi
  · rw [h, Option.getD_some] at hi
    exact hall l (List.mem_of_getElem? h) i hi

private theorem mOf_le (ε : Eps) : mOf ε ≤ 36 := by cases ε <;> decide

private theorem nM_pos (ε : Eps) : 0 < nM ε := by cases ε <;> decide

private def dl (g v : ℕ) : ℕ := v <<< (7 * g)

private theorem testBit_dl (g v t : ℕ) :
    (dl g v).testBit t = (decide (t ≥ 7 * g) && v.testBit (t - 7 * g)) :=
  Nat.testBit_shiftLeft _

private theorem dl_zero (g : ℕ) : dl g 0 = 0 := by simp [dl]

private theorem dl_xor (g a b : ℕ) : dl g (a ^^^ b) = dl g a ^^^ dl g b :=
  Nat.shiftLeft_xor_distrib

private theorem dl_lt {m g v : ℕ} (hg : g < m) (hv : v < 2 ^ 7) : dl g v < 2 ^ (m * 7) := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  rw [testBit_dl, testBit_lt_pow hv (by omega), Bool.and_false]

private theorem dl_expand (g : ℕ) {v : ℕ} (hv : v < 2 ^ 7) :
    dl g v = xorN 7 fun b => if v.testBit b then dl g (2 ^ b) else 0 := by
  conv_lhs => rw [← xorN_bits hv]
  rw [map_xorN (K := 7) (dl_zero g) (fun a b _ _ => dl_xor g a b)
    (fun b hb => by
      split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) hb
      · exact Nat.two_pow_pos _)]
  congr 1
  funext b
  exact ite_map (dl_zero g) _ _

private theorem blkN_dl {v : ℕ} (hv : v < 2 ^ 7) (g h : ℕ) :
    blkN 7 (dl g v) h = if h = g then v else 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_blkN, testBit_dl]
  split_ifs with hh
  · subst hh
    by_cases ht : t < 7
    · simp [ht]
    · simp only [ht, decide_false, Bool.false_and]
      exact (testBit_lt_pow hv (by omega)).symm
  · rw [Nat.zero_testBit]
    by_cases ht : t < 7
    · by_cases hge : 7 * h + t ≥ 7 * g
      · have : 7 ≤ 7 * h + t - 7 * g := by omega
        simp [testBit_lt_pow hv this]
      · simp [hge]
    · simp [ht]

private theorem foldOr_dl {m g v : ℕ} (hg : g < m) (hv : v < 2 ^ 7) :
    foldOr m 7 (fun h => if h = g then v else 0) = dl g v := by
  have hf : ∀ h < m, (if h = g then v else 0) < 2 ^ 7 := fun h _ => by
    split_ifs
    · exact hv
    · positivity
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_foldOr (by norm_num) _ m hf, testBit_dl]
  by_cases hq : t / 7 = g
  · have h1 : t < 7 * m := by omega
    have h2 : t - 7 * g = t % 7 := by omega
    simp [hq, h1, h2, show t ≥ 7 * g by omega]
  · simp only [hq, if_false, Nat.zero_testBit, Bool.and_false]
    by_cases hge : t ≥ 7 * g
    · rw [testBit_lt_pow hv (by omega), Bool.and_false]
    · simp [hge]

private theorem pow_eq_dl (c : ℕ) : 2 ^ c = dl (c / 7) (2 ^ (c % 7)) := by
  rw [dl, Nat.shiftLeft_eq, ← Nat.pow_add, Nat.mod_add_div]

private theorem actM_eq (ε : Eps) (i y : ℕ) :
    actMCode ε i y = foldOr (mOf ε) 7 fun g => actECode ε i (blkN 7 y (permIdx ε i g)) := rfl

private theorem actM_lt (ε : Eps) {i : ℕ} (hi : i < 7) (y : ℕ) : actMCode ε i y < 2 ^ nM ε := by
  rw [actM_eq]
  have := foldOr_lt (k := mOf ε) (n := 7) (by norm_num) _
    (fun g _ => (actE_facts ε hi (blkN_lt 7 y (permIdx ε i g))).1)
  rwa [Nat.mul_comm] at this

private theorem actM_xor (ε : Eps) {i : ℕ} (hi : i < 7) (F G : ℕ) :
    actMCode ε i (F ^^^ G) = actMCode ε i F ^^^ actMCode ε i G := by
  rw [actM_eq, actM_eq, actM_eq, ← foldOr_xor (by norm_num)
    (fun g _ => (actE_facts ε hi (blkN_lt 7 F _)).1) (fun g _ => (actE_facts ε hi (blkN_lt 7 G _)).1)]
  refine foldOr_congr fun g _ => ?_
  rw [blkN_xor, actE_xor ε hi (blkN_lt 7 F _) (blkN_lt 7 G _)]

private theorem actM_dl (ε : Eps) {i g v : ℕ} (hi : i < 7) (hg : g < mOf ε) (hv : v < 2 ^ 7) :
    actMCode ε i (dl g v) = dl (permIdx ε i g) (actECode ε i v) := by
  rw [actM_eq, ← foldOr_dl (perm_facts ε hi hg).1 (actE_facts ε hi hv).1]
  refine foldOr_congr fun h hh => ?_
  rw [blkN_dl hv]
  by_cases e : h = permIdx ε i g
  · rw [if_pos e, if_pos (by rw [e]; exact (perm_facts ε hi hg).2)]
  · rw [if_neg e, if_neg, actE_zero ε hi]
    intro e'
    exact e (by rw [← e']; exact ((perm_facts ε hi hh).2).symm)

private theorem foxM_lt (ε : Eps) {d : ℕ → ℕ} (hd : ∀ i, d i < 2 ^ nM ε) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 7) → foxMCode ε d l < 2 ^ nM ε
  | [], _ => Nat.two_pow_pos _
  | i :: _, hl => Nat.xor_lt_two_pow (hd i) (actM_lt ε (hl i (by simp)) _)

private def pr (ε : Eps) (y : ℕ → ZMod 2) (F : ℕ) : ZMod 2 :=
  ∑ c ∈ range (nM ε), y c * bz (F.testBit c)

private theorem pr_xor (ε : Eps) (y : ℕ → ZMod 2) (F G : ℕ) :
    pr ε y (F ^^^ G) = pr ε y F + pr ε y G := by
  simp only [pr, Nat.testBit_xor, bz_xor, mul_add, sum_add_distrib]

private theorem pr_zero (ε : Eps) (y : ℕ → ZMod 2) : pr ε y 0 = 0 := by simp [pr]

private theorem pr_dl (ε : Eps) (y : ℕ → ZMod 2) {g v : ℕ} (hg : g < mOf ε) (hv : v < 2 ^ 7) :
    pr ε y (dl g v) = ∑ b ∈ range 7, y (7 * g + b) * bz (v.testBit b) := by
  rw [pr, sum_range_mul' (mOf ε) 7, sum_eq_single g]
  · refine sum_congr rfl fun b hb => ?_
    have hb' := mem_range.1 hb
    rw [testBit_dl, Nat.mul_comm g 7]
    simp
  · intro h _ hne
    refine sum_eq_zero fun b hb => ?_
    have hb' := mem_range.1 hb
    rw [testBit_dl]
    by_cases hge : h * 7 + b ≥ 7 * g
    · rw [testBit_lt_pow hv (by omega)]
      simp
    · simp [hge]
  · intro h
    exact absurd (mem_range.2 hg) h

private structure Rep (ε : Eps) (pi mm : ℕ) (T : ℕ → ℕ) : Prop where
  pi_lt : ∀ g < mOf ε, fld 6 pi g < mOf ε
  unit : ∀ g < mOf ε, ∀ b < 7, T (dl g (2 ^ b)) = dl (fld 6 pi g) (fld 7 mm b)
  add : ∀ F G, F < 2 ^ nM ε → G < 2 ^ nM ε → T (F ^^^ G) = T F ^^^ T G
  lt : ∀ F < 2 ^ nM ε, T F < 2 ^ nM ε

private theorem Rep.zero {ε : Eps} {pi mm : ℕ} {T : ℕ → ℕ} (hR : Rep ε pi mm T) : T 0 = 0 := by
  have := hR.add 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  simpa using this

private theorem Rep.apply {ε : Eps} {pi mm : ℕ} {T : ℕ → ℕ} (hR : Rep ε pi mm T) {g v : ℕ}
    (hg : g < mOf ε) (hv : v < 2 ^ 7) : T (dl g v) = dl (fld 6 pi g) (applyM mm v) := by
  have hpow : ∀ b < 7, (2 : ℕ) ^ b < 2 ^ 7 := fun b hb => Nat.pow_lt_pow_right (by norm_num) hb
  rw [dl_expand g hv, map_xorN (K := nM ε) hR.zero hR.add (fun b hb => by
    split_ifs
    · exact dl_lt hg (hpow b hb)
    · exact Nat.two_pow_pos _)]
  rw [applyM, map_xorN (K := 7) (dl_zero _) (fun a b _ _ => dl_xor _ a b) (fun b _ => by
    split_ifs
    · exact fld_lt 7 mm b
    · exact Nat.two_pow_pos _)]
  refine xorN_congr fun b hb => ?_
  rw [ite_map hR.zero, ite_map (dl_zero _), hR.unit g hg b hb]

private theorem applyM_lt (mm v : ℕ) : applyM mm v < 2 ^ 7 :=
  xorN_lt fun b _ => by
    split_ifs
    · exact fld_lt 7 mm b
    · exact Nat.two_pow_pos _

private theorem Rep.step {ε : Eps} {TP TA : ℕ}
    (hTP : ∀ i < 7, ∀ g < mOf ε, fld 6 TP (i * mOf ε + g) = permIdx ε i g)
    (hTA : ∀ i < 7, ∀ x < 128, fld 7 TA (128 * i + x) = actECode ε i x)
    {pi mm : ℕ} {T : ℕ → ℕ} (hR : Rep ε pi mm T) {i : ℕ} (hi : i < 7) :
    Rep ε (stepPi (mOf ε) TP i pi) (stepM TA i mm) (fun F => T (actMCode ε i F)) := by
  have hpi : ∀ g < mOf ε, fld 6 (stepPi (mOf ε) TP i pi) g = fld 6 pi (permIdx ε i g) := by
    intro g hg
    rw [stepPi, packN_eq, fld_foldOr (by norm_num) _ (fun g _ => fld_lt _ _ _) hg, hTP i hi g hg]
  have hmm : ∀ b < 7, fld 7 (stepM TA i mm) b = applyM mm (actECode ε i (2 ^ b)) := by
    intro b hb
    have h2 : 2 ^ b < 128 := by
      have := Nat.pow_lt_pow_right (a := 2) (by norm_num) hb
      simpa using this
    rw [stepM, packN_eq, fld_foldOr (by norm_num) _ (fun b _ => applyM_lt _ _) hb, hTA i hi _ h2]
  refine ⟨fun g hg => ?_, fun g hg b hb => ?_, fun F G hF hG => ?_, fun F hF => ?_⟩
  · rw [hpi g hg]
    exact hR.pi_lt _ (perm_facts ε hi hg).1
  · have hb' : (2 : ℕ) ^ b < 2 ^ 7 := Nat.pow_lt_pow_right (by norm_num) hb
    rw [actM_dl ε hi hg hb', hR.apply (perm_facts ε hi hg).1 (actE_facts ε hi hb').1, hpi g hg,
      hmm b hb]
  · rw [actM_xor ε hi, hR.add _ _ (actM_lt ε hi F) (actM_lt ε hi G)]
  · exact hR.lt _ (actM_lt ε hi F)

private theorem Rep.init (ε : Eps) : Rep ε (pi0 (mOf ε)) mm0 id := by
  have hpi : ∀ g < mOf ε, fld 6 (pi0 (mOf ε)) g = g := by
    intro g hg
    rw [pi0, packN_eq, fld_foldOr (by norm_num) _ (fun g hg => ?_) hg]
    have := mOf_le ε
    have : g < 64 := by omega
    simpa using this
  have hmm : ∀ b < 7, fld 7 mm0 b = 2 ^ b := by
    intro b hb
    exact (by rw [mm0, packN_eq, fld_foldOr (by norm_num) _
      (fun b hb => Nat.pow_lt_pow_right (by norm_num) hb) hb])
  refine ⟨fun g hg => by rw [hpi g hg]; exact hg, fun g hg b hb => ?_, fun _ _ _ _ => rfl,
    fun _ hF => hF⟩
  rw [hpi g hg, hmm b hb]
  rfl

private theorem blkN_unit {n i0 c0 : ℕ} (hc0 : c0 < n) (i : ℕ) :
    blkN n (2 ^ (n * i0 + c0)) i = if i = i0 then 2 ^ c0 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_blkN, Nat.testBit_two_pow]
  split_ifs with hi
  · subst hi
    rw [Nat.testBit_two_pow]
    by_cases ht : t < n
    · simp [ht]
    · simp only [ht, decide_false, Bool.false_and]
      symm
      simp only [decide_eq_false_iff_not]
      omega
  · rw [Nat.zero_testBit]
    by_cases ht : t < n
    · simp only [ht, decide_true, Bool.true_and, decide_eq_false_iff_not]
      intro e
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · have : n * (i + 1) ≤ n * i0 := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        omega
      · have : n * (i0 + 1) ≤ n * i := Nat.mul_le_mul_left _ h
        rw [Nat.mul_succ] at this
        omega
    · simp [ht]

private theorem contrib_fld {m w YBj pi mm c0 : ℕ} (hw : 0 < w) (hc0 : c0 < 7 * m) :
    fld w (contrib m w YBj pi mm) c0 =
      xorN 7 fun b' => if (fld 7 mm (c0 % 7)).testBit b' then
        fld w YBj (7 * fld 6 pi (c0 / 7) + b') else 0 := by
  rw [contrib, packN_eq, fld_foldOr hw _ (fun c _ => xorN_lt fun b _ => by
    split_ifs
    · exact fld_lt _ _ _
    · exact Nat.two_pow_pos _) hc0]

private theorem contrib_lt {m w YBj pi mm : ℕ} (hw : 0 < w) :
    contrib m w YBj pi mm < 2 ^ (w * (7 * m)) := by
  rw [contrib, packN_eq]
  exact foldOr_lt hw _ fun c _ => xorN_lt fun b _ => by
    split_ifs
    · exact fld_lt _ _ _
    · exact Nat.two_pow_pos _

private theorem walk_fld (ε : Eps) {w TP TA k YBj : ℕ} (hk : k < w)
    (hTP : ∀ i < 7, ∀ g < mOf ε, fld 6 TP (i * mOf ε + g) = permIdx ε i g)
    (hTA : ∀ i < 7, ∀ x < 128, fld 7 TA (128 * i + x) = actECode ε i x)
    {i0 c0 : ℕ} (hc0 : c0 < nM ε) (l : List ℕ) (hl : ∀ i ∈ l, i < 7) :
    ∀ pi mm acc (T : ℕ → ℕ), Rep ε pi mm T →
      bz ((fld w (walk (mOf ε) w TP TA YBj l pi mm acc) (nM ε * i0 + c0)).testBit k) =
        bz ((fld w acc (nM ε * i0 + c0)).testBit k) +
          pr ε (fun c => bz ((fld w YBj c).testBit k))
            (T (foxMCode ε (blkN (nM ε) (2 ^ (nM ε * i0 + c0))) l)) := by
  have hw : 0 < w := by omega
  have hN : 7 * mOf ε = nM ε := Nat.mul_comm _ _
  induction l with
  | nil =>
    intro pi mm acc T hR
    simp [walk, foxMCode, hR.zero, pr_zero]
  | cons i l ih =>
    intro pi mm acc T hR
    have hi : i < 7 := hl i (by simp)
    have hd : ∀ i, blkN (nM ε) (2 ^ (nM ε * i0 + c0)) i < 2 ^ nM ε := fun i => blkN_lt _ _ _
    have hfox := foxM_lt ε hd l fun j hj => hl j (by simp [hj])
    have ih' := ih (fun j hj => hl j (by simp [hj])) _ _
      (acc ^^^ (contrib (mOf ε) w YBj pi mm <<< (w * (7 * mOf ε) * i))) _ (hR.step hTP hTA hi)
    change bz ((fld w (walk (mOf ε) w TP TA YBj l (stepPi (mOf ε) TP i pi) (stepM TA i mm)
      (acc ^^^ (contrib (mOf ε) w YBj pi mm <<< (w * (7 * mOf ε) * i)))) _).testBit k) = _
    rw [ih', fld_xor, hN]
    rw [fld_shift (by rw [← hN]; exact contrib_lt hw) i i0 hc0]
    simp only [foxMCode]
    rw [hR.add _ _ (hd i) (actM_lt ε hi _), pr_xor, Nat.testBit_xor, bz_xor, add_assoc]
    congr 2
    rw [blkN_unit hc0]
    split_ifs with hii
    · subst hii
      have hg : c0 / 7 < mOf ε := by
        have : c0 < mOf ε * 7 := hc0
        omega
      have hb : c0 % 7 < 7 := Nat.mod_lt _ (by norm_num)
      rw [contrib_fld hw (by rw [hN]; exact hc0), bz_xorN, pow_eq_dl c0,
        hR.unit _ hg _ hb, pr_dl ε _ (hR.pi_lt _ hg) (fld_lt _ _ _)]
      refine sum_congr rfl fun b _ => ?_
      rw [bz_ite, mul_comm]
    · rw [hR.zero, pr_zero]
      simp

private theorem accN_fld (ε : Eps) {w TP TA k : ℕ} {YB : ℕ → ℕ} (hk : k < w)
    (hTP : ∀ i < 7, ∀ g < mOf ε, fld 6 TP (i * mOf ε + g) = permIdx ε i g)
    (hTA : ∀ i < 7, ∀ x < 128, fld 7 TA (128 * i + x) = actECode ε i x)
    {i0 c0 : ℕ} (hc0 : c0 < nM ε) (N : ℕ) :
    bz ((fld w (accN (mOf ε) w TP TA YB N) (nM ε * i0 + c0)).testBit k) =
      ∑ j ∈ range N, pr ε (fun c => bz ((fld w (YB j) c).testBit k))
        (foxMCode ε (blkN (nM ε) (2 ^ (nM ε * i0 + c0))) (relWords.getD j [])) := by
  induction N with
  | zero => simp [accN, fld_zero]
  | succ N ih =>
    change bz ((fld w (walk (mOf ε) w TP TA (YB N) (relWords.getD N []) (pi0 (mOf ε)) mm0
      (accN (mOf ε) w TP TA YB N)) _).testBit k) = _
    rw [walk_fld ε hk hTP hTA hc0 _ (relWords_lt N) _ _ _ _ (Rep.init ε), ih, sum_range_succ]
    rfl

private def Ymat (ε : Eps) (w ny : ℕ) (YB : ℕ → ℕ) : Array ℕ :=
  Array.ofFn (n := ny) fun k =>
    bitsOf (29 * nM ε) fun r => (fld w (YB (r / nM ε)) (r % nM ε)).testBit k

private theorem Ymat_bit (ε : Eps) {w ny k : ℕ} {YB : ℕ → ℕ} (hk : k < ny) {j c : ℕ}
    (hj : j < 29) (hc : c < nM ε) :
    ((Ymat ε w ny YB).getD k 0).testBit (j * nM ε + c) = (fld w (YB j) c).testBit k := by
  rw [Ymat, getD_ofFn' _ hk, testBit_bitsOf, (divmod_aux hc).1, (divmod_aux hc).2]
  simp [lt_block hj hc]

private theorem fmMat_bit (ε : Eps) {r col : ℕ} (hr : r < 29 * nM ε) :
    ((fmMat ε).getD r 0).testBit col =
      (decide (col < 7 * nM ε) && (foxMb ε (2 ^ col)).testBit r) := by
  rw [fmMat, linBits, btr, getD_ofFn' _ hr, testBit_bitsOf]
  by_cases hc : col < 7 * nM ε
  · simp [hc, getD_ofFn' _ hc]
  · simp [hc]

private theorem iotaMat_bit (ε : Eps) {r c : ℕ} (hr : r < 29 * nM ε) :
    ((iotaMat ε).getD r 0).testBit c = (decide (c < 203) && (iotaB ε (2 ^ c)).testBit r) := by
  rw [iotaMat, linBits, btr, getD_ofFn' _ hr, testBit_bitsOf]
  by_cases hc : c < 203
  · simp [hc, getD_ofFn' _ hc]
  · simp [hc]

private theorem foxMb_bit (ε : Eps) (v : ℕ) {j c : ℕ} (hj : j < 29) (hc : c < nM ε) :
    (foxMb ε v).testBit (j * nM ε + c) =
      (foxMCode ε (blkN (nM ε) v) (relWords.getD j [])).testBit c := by
  rw [foxMb, testBit_foldOr (nM_pos ε) _ 29
    (fun j _ => foxM_lt ε (fun _ => blkN_lt _ _ _) _ (relWords_lt j)),
    (divmod_aux hc).1, (divmod_aux hc).2]
  have := lt_block hj hc
  simp [show j * nM ε + c < nM ε * 29 by rw [Nat.mul_comm (nM ε)]; exact this]

private theorem constM_bit (ε : Eps) {x c : ℕ} (hx : x < 2 ^ 7) (hc : c < nM ε) :
    (constM ε x).testBit c = x.testBit (c % 7) := by
  rw [constM, testBit_foldOr (by norm_num) _ (mOf ε) (fun _ _ => hx)]
  have : c < 7 * mOf ε := by rw [Nat.mul_comm]; exact hc
  simp [this]

private theorem constM_lt (ε : Eps) {x : ℕ} (hx : x < 2 ^ 7) : constM ε x < 2 ^ nM ε := by
  have := foldOr_lt (k := mOf ε) (n := 7) (by norm_num) (fun _ => x) (fun _ _ => hx)
  rw [Nat.mul_comm] at this
  exact this

private theorem iotaB_bit (ε : Eps) (v : ℕ) {j c : ℕ} (hj : j < 29) (hc : c < nM ε) :
    (iotaB ε v).testBit (j * nM ε + c) = (blkN 7 v j).testBit (c % 7) := by
  rw [iotaB, testBit_foldOr (nM_pos ε) _ 29 (fun j _ => constM_lt ε (blkN_lt 7 v j)),
    (divmod_aux hc).1, (divmod_aux hc).2, constM_bit ε (blkN_lt 7 v j) hc]
  have := lt_block hj hc
  simp [show j * nM ε + c < nM ε * 29 by rw [Nat.mul_comm (nM ε)]; exact this]

private theorem fm_row_zero (ε : Eps) {w ny TP TA : ℕ} {YB : ℕ → ℕ} (hw : ny ≤ w)
    (hTP : ∀ i < 7, ∀ g < mOf ε, fld 6 TP (i * mOf ε + g) = permIdx ε i g)
    (hTA : ∀ i < 7, ∀ x < 128, fld 7 TA (128 * i + x) = actECode ε i x)
    (hacc : accN (mOf ε) w TP TA YB 29 = 0) {k : ℕ} (hk : k < ny) :
    rowMul (29 * nM ε) ((Ymat ε w ny YB).getD k 0) (fmMat ε) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro col
  rw [Nat.zero_testBit, testBit_rowMul]
  apply bz_injective
  rw [bz_xorFold_range, bz_false, sum_range_mul' 29 (nM ε)]
  by_cases hcol : col < 7 * nM ε
  · have hc0 : col % nM ε < nM ε := Nat.mod_lt _ (nM_pos ε)
    have h := accN_fld ε (YB := YB) (lt_of_lt_of_le hk hw) hTP hTA (i0 := col / nM ε) hc0 29
    rw [hacc, fld_zero, Nat.zero_testBit, bz_false, Nat.div_add_mod] at h
    refine Eq.trans ?_ h.symm
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    refine sum_congr rfl fun c hc => ?_
    have hc' := mem_range.1 hc
    rw [bz_and, Ymat_bit ε hk hj' hc', fmMat_bit ε (lt_block hj' hc'), foxMb_bit ε _ hj' hc']
    simp [hcol]
  · refine sum_eq_zero fun j hj => sum_eq_zero fun c hc => ?_
    rw [fmMat_bit ε (lt_block (mem_range.1 hj) (mem_range.1 hc))]
    simp [hcol]

private theorem iota_row (ε : Eps) {w ny : ℕ} {YB : ℕ → ℕ} {k : ℕ} (hk : k < ny) :
    rowMul (29 * nM ε) ((Ymat ε w ny YB).getD k 0) (iotaMat ε) =
      bitsOf 203 fun c => (xorN (mOf ε) fun g => fld w (YB (c / 7)) (7 * g + c % 7)).testBit k := by
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_rowMul, testBit_bitsOf]
  apply bz_injective
  rw [bz_xorFold_range, sum_range_mul' 29 (nM ε)]
  by_cases hc : c < 203
  · rw [decide_eq_true hc, Bool.true_and, bz_xorN]
    have hj0 : c / 7 < 29 := by omega
    rw [sum_eq_single (c / 7)]
    · rw [sum_range_mul' (mOf ε) 7]
      refine sum_congr rfl fun g hg => ?_
      have hg' := mem_range.1 hg
      have hgc : g * 7 + c % 7 < nM ε := by
        have := Nat.mod_lt c (show 7 > 0 by norm_num)
        show g * 7 + c % 7 < mOf ε * 7
        omega
      rw [sum_eq_single (c % 7)]
      · have e : c = 7 * (c / 7) + c % 7 := (Nat.div_add_mod c 7).symm
        rw [bz_and, Ymat_bit ε hk hj0 hgc, iotaMat_bit ε (lt_block hj0 hgc), iotaB_bit ε _ hj0 hgc,
          Nat.mul_add_mod_of_lt (Nat.mod_lt c (by norm_num)), testBit_blkN, Nat.testBit_two_pow,
          decide_eq_true hc, decide_eq_true (Nat.mod_lt c (by norm_num)), decide_eq_true e,
          Nat.mul_comm g 7]
        simp
      · intro b hb hne
        have hb' := mem_range.1 hb
        have hgb : g * 7 + b < nM ε := by show g * 7 + b < mOf ε * 7; omega
        rw [bz_and, iotaMat_bit ε (lt_block hj0 hgb), iotaB_bit ε _ hj0 hgb,
          Nat.mul_add_mod_of_lt hb', testBit_blkN, Nat.testBit_two_pow]
        have : ¬ (c = 7 * (c / 7) + b) := by omega
        simp [hc, this]
      · intro h
        exact absurd (mem_range.2 (Nat.mod_lt c (by norm_num))) h
    · intro j hj hne
      have hj' := mem_range.1 hj
      refine sum_eq_zero fun c' hc' => ?_
      have hc'' := mem_range.1 hc'
      rw [bz_and, iotaMat_bit ε (lt_block hj' hc''), iotaB_bit ε _ hj' hc'', testBit_blkN,
        Nat.testBit_two_pow]
      have : ¬ (c = 7 * j + c' % 7) := by omega
      simp [hc, this]
    · intro h
      exact absurd (mem_range.2 hj0) h
  · rw [decide_eq_false hc, Bool.false_and, bz_false]
    refine sum_eq_zero fun j hj => sum_eq_zero fun c' hc' => ?_
    rw [iotaMat_bit ε (lt_block (mem_range.1 hj) (mem_range.1 hc'))]
    simp [hc]

theorem ySplit_sound (ε : Eps) {w ny TP TA : ℕ} {YB : ℕ → ℕ} (h : ySplitOK ε w ny TP TA YB = true) :
    ∃ Y : Array ℕ, splitTest ε (29 * nM ε) (fmMat ε) (iotaMat ε) Y = true := by
  simp only [ySplitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allN_eq_true] at h
  obtain ⟨⟨⟨⟨hw, hTP⟩, hTA⟩, hacc⟩, hcert⟩ := h
  refine ⟨Ymat ε w ny YB, ?_⟩
  have hsize : (Ymat ε w ny YB).size = ny := Array.size_ofFn
  rw [splitTest, hsize, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simp only [bIsZero, List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi
    rw [bmul, getD_ofFn' _ hi]
    exact fm_row_zero ε hw hTP hTA hacc hi
  · have : bmul ny (29 * nM ε) (Ymat ε w ny YB) (iotaMat ε) = yiRows (mOf ε) w ny YB := by
      rw [bmul, yiRows]
      congr 1
      funext k
      exact iota_row ε k.isLt
    rw [this]
    exact hcert

end CFSG.KC.O8Split

end
