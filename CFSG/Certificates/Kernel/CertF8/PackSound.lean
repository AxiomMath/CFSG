module

public import Certificates.Data.Kernel.CertF8.Pack
public import CFSG.Certificates.Kernel.G28.Sound

public section

namespace CFSG.KC.CertF8

open CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.KC.G28 (fld letN letN_eq mx idP letterP codeP codeP_bit codeP_lt codeP_inj codeP_idCode
  codeP_letterCode mx_field mt_bit mulCode_get testBit_of_lt)
open CFSG.KC.Misc.G2U (pk pk_nil pk_cons_eq pk_lt testBit_pk)

@[expose] def bxr (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => bxr f k ^^ f k

theorem bxr_false (n : ℕ) : bxr (fun _ => false) n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bxr, ih]

theorem mulG_bit (n e W L F a : ℕ) (Xs : List ℕ) (q : ℕ) :
    (mulG n e W L F a Xs).testBit q = bxr (fun k => (termsL a k e W L F Xs 0).testBit q) n := by
  induction n with
  | zero => simp [mulG, bxr]
  | succ n ih =>
    change ((mulG n e W L F a Xs) ^^^ termsL a n e W L F Xs 0).testBit q = _
    rw [Nat.testBit_xor, ih]
    rfl

theorem pk_mul {W c : ℕ} {m : List ℕ} (h : ∀ x ∈ m, x < 2 ^ W ∧ x * c < 2 ^ W) :
    pk W m * c = pk W (m.map (· * c)) := by
  induction m with
  | nil => simp [pk_nil]
  | cons r t ih =>
    have hr := h r (List.mem_cons_self ..)
    rw [pk_cons_eq hr.1, List.map_cons, pk_cons_eq hr.2,
      ← ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    ring

theorem fld_eq (x o m : ℕ) : fld x o m = (x >>> o) % 2 ^ m := by
  change (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_lt (x o m : ℕ) : fld x o m < 2 ^ m := by
  rw [fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos m)

theorem fld_testBit (x o m q : ℕ) (hq : q < m) : (fld x o m).testBit q = x.testBit (o + q) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hq]

theorem decomp {W n q : ℕ} (hW : 0 < W) (hq : q < W * n) :
    ∃ i p, i < n ∧ p < W ∧ q = W * i + p :=
  ⟨q / W, q % W, (Nat.div_lt_iff_lt_mul hW).2 (by rw [Nat.mul_comm]; exact hq), Nat.mod_lt _ hW,
    (Nat.div_add_mod q W).symm⟩

theorem one_lt_two_pow' {W : ℕ} (hW : 0 < W) : (1 : ℕ) < 2 ^ W :=
  Nat.one_lt_two_pow (by omega)

theorem land_L {W n L : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1)) (y : ℕ) :
    Nat.land y L = pk W ((List.range n).map fun i => if y.testBit (W * i) then 1 else 0) := by
  have h1 := one_lt_two_pow' hW
  have hm : ∀ x ∈ (List.range n).map (fun i => if y.testBit (W * i) then 1 else 0), x < 2 ^ W := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    split <;> omega
  have hr : ∀ x ∈ List.replicate n 1, x < 2 ^ W := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact h1
  apply Nat.eq_of_testBit_eq
  intro q
  change (y &&& L).testBit q = _
  rw [Nat.testBit_and, hL]
  by_cases hq : q < W * n
  · obtain ⟨i, k, hi, hk, rfl⟩ := decomp hW hq
    rw [testBit_pk hr i hk, testBit_pk hm i hk, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate, List.getElem_map,
      List.getElem_range]
    rcases k with _ | k
    · by_cases hy : y.testBit (W * i) <;> simp [hy]
    · by_cases hy : y.testBit (W * i) <;> simp [hy, Nat.testBit_add_one]
  · have hle : 2 ^ (W * n) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 := pk_lt hr
    have e2 := pk_lt hm
    simp only [List.length_replicate, List.length_map, List.length_range] at e1 e2
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le e1 hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le e2 hle)]
    simp

theorem rep_eq {W n L r : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1)) (hr : r < 2 ^ W) :
    Nat.mul r L = pk W (List.replicate n r) := by
  change r * L = _
  rw [Nat.mul_comm, hL, pk_mul (fun x hx => by
    rw [List.eq_of_mem_replicate hx, Nat.one_mul]
    exact ⟨one_lt_two_pow' hW, hr⟩), List.map_replicate, Nat.one_mul]

theorem rep_lt {W n L r : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1)) (hr : r < 2 ^ W) :
    Nat.mul r L < 2 ^ (W * n) := by
  rw [rep_eq hW hL hr]
  have h := pk_lt (w := W) (m := List.replicate n r) (fun x hx => by
    rw [List.eq_of_mem_replicate hx]
    exact hr)
  rwa [List.length_replicate] at h

theorem term_bit {n W L F : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1))
    (hF : F = 2 ^ W - 1) (a o X o' : ℕ) {i p : ℕ} (hi : i < n) (hp : p < W) :
    (Nat.land (spr a o L F) (Nat.mul (fld X o' W) L)).testBit (W * i + p) =
      (a.testBit (o + W * i) && X.testBit (o' + p)) := by
  have hF' : F < 2 ^ W := by
    rw [hF]
    exact Nat.sub_lt (Nat.two_pow_pos W) (by norm_num)
  have hm : ∀ x ∈ (List.range n).map (fun i => if (Nat.shiftRight a o).testBit (W * i) then 1 else 0),
      x < 2 ^ W ∧ x * F < 2 ^ W := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    split
    · exact ⟨one_lt_two_pow' hW, by omega⟩
    · exact ⟨Nat.two_pow_pos W, by simp⟩
  have hm2 : ∀ x ∈ ((List.range n).map
      (fun i => if (Nat.shiftRight a o).testBit (W * i) then 1 else 0)).map (· * F), x < 2 ^ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (hm y hy).2
  have hr : ∀ x ∈ List.replicate n (fld X o' W), x < 2 ^ W := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact fld_lt _ _ _
  change (Nat.mul (Nat.land (Nat.shiftRight a o) L) F &&& Nat.mul (fld X o' W) L).testBit _ = _
  rw [Nat.testBit_and, rep_eq hW hL (fld_lt _ _ _), land_L hW hL]
  change ((pk W _ * F).testBit _ && _) = _
  rw [pk_mul hm, testBit_pk hm2 i hp, testBit_pk hr i hp,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_replicate, List.getElem_map, List.getElem_map, List.getElem_range,
    fld_testBit _ _ _ _ hp]
  change (((if (a >>> o).testBit (W * i) then 1 else 0) * F).testBit p && _) = _
  rw [Nat.testBit_shiftRight, hF]
  by_cases h : a.testBit (o + W * i)
  · simp [h, Nat.testBit_two_pow_sub_one, hp]
  · simp [h]

theorem term_bit_hi {n W L F : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1))
    (a o X o' : ℕ) {q : ℕ} (hq : W * n ≤ q) :
    (Nat.land (spr a o L F) (Nat.mul (fld X o' W) L)).testBit q = false := by
  change Nat.testBit (spr a o L F &&& Nat.mul (fld X o' W) L) q = false
  rw [Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le (rep_lt hW hL (fld_lt X o' W))
    (Nat.pow_le_pow_right (by norm_num) hq))]
  simp

theorem termsL_bit_hi {n W L F : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1))
    (a k e : ℕ) (Xs : List ℕ) {q : ℕ} (hq : W * n ≤ q) :
    ∀ b, (termsL a k e W L F Xs b).testBit q = false := by
  induction Xs with
  | nil => intro b; simp [termsL]
  | cons X Xs ih =>
    intro b
    change (Nat.land (spr a (Nat.add (Nat.mul e k) b) L F) (Nat.mul (fld X (Nat.mul W k) W) L) ^^^
      termsL a k e W L F Xs (Nat.succ b)).testBit q = false
    rw [Nat.testBit_xor, term_bit_hi hW hL _ _ _ _ hq, ih]
    rfl

theorem mulG_bit_hi {n e W L F : ℕ} (hW : 0 < W) (hL : L = pk W (List.replicate n 1))
    (a : ℕ) (Xs : List ℕ) {q : ℕ} (hq : W * n ≤ q) : (mulG n e W L F a Xs).testBit q = false := by
  rw [mulG_bit]
  have : (fun k => (termsL a k e W L F Xs 0).testBit q) = fun _ => false :=
    funext fun k => termsL_bit_hi hW hL a k e Xs hq 0
  rw [this, bxr_false]

theorem termsL3 (a k e W L F X0 X1 X2 q : ℕ) :
    (termsL a k e W L F [X0, X1, X2] 0).testBit q =
      ((Nat.land (spr a (e * k) L F) (Nat.mul (fld X0 (W * k) W) L)).testBit q ^^
        ((Nat.land (spr a (e * k + 1) L F) (Nat.mul (fld X1 (W * k) W) L)).testBit q ^^
          (Nat.land (spr a (e * k + 2) L F) (Nat.mul (fld X2 (W * k) W) L)).testBit q)) := by
  change (_ ^^^ (_ ^^^ (_ ^^^ 0))).testBit q = _
  simp only [Nat.testBit_xor, Nat.zero_testBit, Bool.xor_false]
  rfl

theorem L6_eq : L6 = pk 18 (List.replicate 6 1) := by decide +kernel

theorem F18_eq : F18 = 2 ^ 18 - 1 := by decide +kernel

theorem codeP_mulCode6 {A B : Array ℕ} (hA : Valid A) (hB : Valid B) :
    codeP (mulCode A B) = mulS6 (codeP A) (codeP B) := by
  simp only [mulS6, letN_eq]
  have hb0 : ∀ t < 36, ∀ s < 3, (codeP B).testBit (3 * t + s) = (B[t]!).testBit s :=
    fun t _ s hs => codeP_bit hB t s hs
  have hb1 : ∀ t < 36, ∀ s < 3, (mx (codeP B)).testBit (3 * t + s) = (mx B[t]!).testBit s :=
    fun t ht => mx_field _ _ t ht (hb0 t ht)
  have hb2 : ∀ t < 36, ∀ s < 3,
      (mx (mx (codeP B))).testBit (3 * t + s) = (mx (mx B[t]!)).testBit s :=
    fun t ht => mx_field _ _ t ht (hb1 t ht)
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 108
  · obtain ⟨i, j, s, hi, hj, hs, rfl⟩ : ∃ i j s, i < 6 ∧ j < 6 ∧ s < 3 ∧ p = 18 * i + (3 * j + s) :=
      ⟨p / 18, p % 18 / 3, p % 3, by omega, by omega, by omega, by omega⟩
    have hT : ∀ k < 6, (termsL (codeP A) k 3 18 L6 F18
        [codeP B, mx (codeP B), mx (mx (codeP B))] 0).testBit (18 * i + (3 * j + s)) =
        (mt A[6 * i + k]! B[6 * k + j]!).testBit s := by
      intro k hk
      have hq : 3 * j + s < 18 := by omega
      rw [termsL3, term_bit (by norm_num) L6_eq F18_eq _ _ _ _ hi hq,
        term_bit (by norm_num) L6_eq F18_eq _ _ _ _ hi hq,
        term_bit (by norm_num) L6_eq F18_eq _ _ _ _ hi hq]
      have e0 : 3 * k + 18 * i = 3 * (6 * i + k) + 0 := by omega
      have e1 : 3 * k + 1 + 18 * i = 3 * (6 * i + k) + 1 := by omega
      have e2 : 3 * k + 2 + 18 * i = 3 * (6 * i + k) + 2 := by omega
      have e3 : 18 * k + (3 * j + s) = 3 * (6 * k + j) + s := by omega
      rw [e0, e1, e2, e3, codeP_bit hA _ 0 (by omega), codeP_bit hA _ 1 (by omega),
        codeP_bit hA _ 2 (by omega), hb0 _ (by omega) s hs, hb1 _ (by omega) s hs,
        hb2 _ (by omega) s hs]
      exact (mt_bit (hA.2 _ (by omega)) (hB.2 _ (by omega)) hs).symm
    rw [mulG_bit]
    have e : 18 * i + (3 * j + s) = 3 * (6 * i + j) + s := by omega
    rw [e, codeP_bit (valid_mulCode hA hB) _ s hs, mulCode_get hi hj, ← e]
    simp only [bxr]
    rw [hT 0 (by omega), hT 1 (by omega), hT 2 (by omega), hT 3 (by omega), hT 4 (by omega),
      hT 5 (by omega), mulEntry]
    simp only [Nat.testBit_xor, Bool.false_xor, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
      Nat.mul_one, Nat.reduceMul]
  · rw [testBit_of_lt (codeP_lt (valid_mulCode hA hB)) (by omega),
      mulG_bit_hi (by norm_num) L6_eq _ _ (by omega)]

theorem codeP_foldl6 (w : List ℕ) {A : Array ℕ} (hA : Valid A) :
    codeP (w.foldl (fun A n => mulCode A (letterCode n)) A) =
      w.foldl (fun x n => mulS6 x (letterP n)) (codeP A) := by
  induction w generalizing A with
  | nil => rfl
  | cons n w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (valid_mulCode hA (valid_letterCode n)),
      codeP_mulCode6 hA (valid_letterCode n), codeP_letterCode]

theorem codeP_wordCode6 (w : List ℕ) : codeP (wordCode w) = wordS6 w := by
  rw [wordCode, wordS6, codeP_foldl6 w valid_idCode, codeP_idCode]

theorem codeP_powCode6 {A : Array ℕ} (hA : Valid A) (k : ℕ) :
    codeP (powCode A k) = powS6 (codeP A) k := by
  induction k with
  | zero => exact codeP_idCode
  | succ k ih =>
    change codeP (mulCode (powCode A k) A) = mulS6 (powS6 (codeP A) k) (codeP A)
    rw [codeP_mulCode6 (valid_powCode hA k) hA, ih]

end CFSG.KC.CertF8

end
