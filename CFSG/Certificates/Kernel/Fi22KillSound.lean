module

public import Certificates.Data.Kernel.Fi22Kill
public import CFSG.Certificates.Kernel.HOrbSound
public import Mathlib.RingTheory.AdjoinRoot
import CFSG.Certificates.Kernel.Co2KillSound
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Algebra.Field.ZMod

public section

set_option exponentiation.threshold 2048

namespace CFSG.Certificates.Fi22Kill

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates.LCE
  CFSG.Certificates.HO

abbrev F4 : Type := AdjoinRoot (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))

noncomputable abbrev om : F4 := AdjoinRoot.root _

@[expose] noncomputable def bit4 (X k : ℕ) : F4 := ((Nat.land (Nat.shiftRight X k) 1 : ℕ) : F4)

@[expose] noncomputable def dec4 (X : ℕ) : Matrix (Fin 27) (Fin 27) F4 :=
  fun i j => bit4 X (27 * i.val + j.val) + bit4 X (729 + 27 * i.val + j.val) * om

@[expose] def decN (N : ℕ) : Fin 7 → ℤ :=
  fun q => ((Nat.land (Nat.shiftRight N (16 * q.val)) 65535 : ℕ) : ℤ) - 32768

section Mat

open CFSG.KC.MonsterConv.MatChain CFSG.KC.MonsterConv.Orb

private def bs (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bs f n + f n * 2 ^ (27 * n)

private theorem bs_lt {f : ℕ → ℕ} (hf : ∀ r, f r < 2 ^ 27) : ∀ n, bs f n < 2 ^ (27 * n)
  | 0 => by simp [bs]
  | n + 1 => by
    have ih := bs_lt hf n
    have h1 : (f n + 1) * 2 ^ (27 * n) ≤ 2 ^ 27 * 2 ^ (27 * n) := Nat.mul_le_mul_right _ (hf n)
    have e : 2 ^ (27 * (n + 1)) = 2 ^ 27 * 2 ^ (27 * n) := by rw [← pow_add]; ring_nf
    rw [bs, e]
    rw [add_mul, one_mul] at h1
    omega

private theorem bs_bit {f : ℕ → ℕ} (hf : ∀ r, f r < 2 ^ 27) :
    ∀ n i j, i < n → j < 27 → (bs f n).testBit (27 * i + j) = (f i).testBit j
  | 0, i, j, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, j, hi, hj => by
    have e : bs f (n + 1) = 2 ^ (27 * n) * f n + bs f n := by rw [bs]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (bs_lt hf n)]
    split_ifs with hlt
    · exact bs_bit hf n i j (by omega) hj
    · have hin : i = n := by omega
      subst hin
      congr 1
      omega

private theorem bs_mul (f : ℕ → ℕ) (c : ℕ) : ∀ n, bs f n * c = bs (fun r => f r * c) n
  | 0 => by simp [bs]
  | n + 1 => by
    rw [bs, bs, ← bs_mul f c n]
    ring

private theorem bit_hi {x n q : ℕ} (hx : x < 2 ^ n) (hq : n ≤ q) : x.testBit q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hq))

private theorem lows_eq : lows 27 = bs (fun _ => 1) 27 := by decide +kernel

private theorem testBit_one_pos {j : ℕ} (hj : 0 < j) : (1 : ℕ).testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))

private theorem sel_eq (A l : ℕ) :
    Nat.land (Nat.shiftRight A l) (lows 27) =
      bs (fun r => if A.testBit (27 * r + l) then 1 else 0) 27 := by
  have hf : ∀ r, (if A.testBit (27 * r + l) then 1 else 0) < 2 ^ 27 := by
    intro r
    split_ifs <;> norm_num
  have h1 : ∀ r, (fun _ : ℕ => (1 : ℕ)) r < 2 ^ 27 := fun _ => by norm_num
  apply Nat.eq_of_testBit_eq
  intro q
  change (A >>> l &&& lows 27).testBit q = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, lows_eq]
  rcases Nat.lt_or_ge q 729 with hq | hq
  · have eq : q = 27 * (q / 27) + q % 27 := (Nat.div_add_mod q 27).symm
    have hi : q / 27 < 27 := by omega
    have hj : q % 27 < 27 := Nat.mod_lt _ (by norm_num)
    rw [eq, bs_bit h1 27 _ _ hi hj, bs_bit hf 27 _ _ hi hj]
    rcases Nat.eq_zero_or_pos (q % 27) with h0 | h0
    · rw [h0]
      simp only [Nat.testBit_zero, Nat.add_zero]
      split_ifs with hA
      · rw [show l + 27 * (q / 27) = 27 * (q / 27) + l by ring, hA]
        rfl
      · rw [show l + 27 * (q / 27) = 27 * (q / 27) + l by ring]
        simp [hA]
    · rw [testBit_one_pos h0, Bool.and_false]
      split_ifs
      · exact (testBit_one_pos h0).symm
      · simp
  · rw [bit_hi (bs_lt h1 27) (by omega), bit_hi (bs_lt hf 27) (by omega), Bool.and_false]

private theorem fld_lt (B o : ℕ) : fldW B o 27 < 2 ^ 27 := by
  change B >>> o &&& (1 <<< 27 - 1) < 2 ^ 27
  exact Nat.and_lt_two_pow _ (by norm_num)

private theorem fld_bit (B o j : ℕ) (hj : j < 27) : (fldW B o 27).testBit j = B.testBit (o + j) := by
  change (B >>> o &&& (1 <<< 27 - 1)).testBit j = _
  rw [show (1 <<< 27 - 1 : ℕ) = 2 ^ 27 - 1 by norm_num, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  simp [hj]

private noncomputable def term (A B l : ℕ) : ℕ :=
  Nat.land (Nat.mul (Nat.land (Nat.shiftRight A l) (lows 27)) (nat_lit 134217727))
    (Nat.mul (fldW B (Nat.mul (nat_lit 27) l) (nat_lit 27)) (lows 27))

private theorem O_eq : (134217727 : ℕ) = 2 ^ 27 - 1 := by norm_num

private theorem term_spec (A B l : ℕ) :
    term A B l < 2 ^ 729 ∧ ∀ i j, i < 27 → j < 27 →
      (term A B l).testBit (27 * i + j) = (A.testBit (27 * i + l) && B.testBit (27 * l + j)) := by
  set a : ℕ → ℕ := fun r => if A.testBit (27 * r + l) then 1 else 0 with hadef
  have hx : Nat.mul (Nat.land (Nat.shiftRight A l) (lows 27)) (nat_lit 134217727) =
      bs (fun r => a r * 134217727) 27 := by
    change Nat.land (Nat.shiftRight A l) (lows 27) * 134217727 = _
    rw [sel_eq A l, bs_mul]
  have hy : Nat.mul (fldW B (Nat.mul (nat_lit 27) l) (nat_lit 27)) (lows 27) =
      bs (fun _ => 1 * fldW B (27 * l) 27) 27 := by
    change fldW B (27 * l) 27 * lows 27 = _
    rw [lows_eq, Nat.mul_comm, bs_mul]
  have hfx : ∀ r, a r * 134217727 < 2 ^ 27 := by
    intro r
    simp only [hadef]
    split_ifs <;> norm_num
  have hfy : ∀ r, (fun _ : ℕ => 1 * fldW B (27 * l) 27) r < 2 ^ 27 := fun _ => by
    rw [one_mul]
    exact fld_lt _ _
  have ht : term A B l = bs (fun r => a r * 134217727) 27 &&& bs (fun _ => 1 * fldW B (27 * l) 27) 27 := by
    unfold term
    rw [hx, hy]
    rfl
  refine ⟨by rw [ht]; exact Nat.and_lt_two_pow _ (bs_lt hfy 27), fun i j hi hj => ?_⟩
  rw [ht, Nat.testBit_and, bs_bit hfx 27 i j hi hj, bs_bit hfy 27 i j hi hj, one_mul,
    fld_bit _ _ _ hj, O_eq]
  simp only [hadef]
  split_ifs with hA
  · rw [hA, one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true hj, Bool.true_and]
  · rw [Bool.not_eq_true] at hA
    rw [hA, zero_mul, Nat.zero_testBit, Bool.false_and]

private noncomputable def chi (b : Bool) : F4 := if b then 1 else 0

private theorem two_F4 : (2 : F4) = 0 := by
  have h : (2 : F4) = AdjoinRoot.of _ (2 : ZMod 2) := (map_ofNat _ 2).symm
  rw [h, show (2 : ZMod 2) = 0 from rfl, map_zero]

private theorem chi_xor (a b : Bool) : chi (a ^^ b) = chi a + chi b := by
  cases a <;> cases b <;> simp [chi]
  first | linear_combination two_F4 | linear_combination -two_F4

private theorem chi_and (a b : Bool) : chi (a && b) = chi a * chi b := by
  cases a <;> cases b <;> simp [chi]

private theorem bit4_eq (X k : ℕ) : bit4 X k = chi (X.testBit k) := by
  unfold bit4 chi
  change ((X >>> k &&& 1 : ℕ) : F4) = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ k) with h | h <;> simp [h]

private theorem m2_spec (A B : ℕ) :
    m2 A B < 2 ^ 729 ∧ ∀ i j, i < 27 → j < 27 → chi ((m2 A B).testBit (27 * i + j)) =
      ∑ l : Fin 27, chi (A.testBit (27 * i + l.val)) * chi (B.testBit (27 * l.val + j)) := by
  set P : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) 0
    (fun l acc => Nat.xor acc (term A B l)) n with hP
  have hm : m2 A B = P 27 := rfl
  have key : ∀ n ≤ 27, P n < 2 ^ 729 ∧ ∀ q, chi ((P n).testBit q) =
      ∑ l ∈ Finset.range n, chi ((term A B l).testBit q) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simp [hP], fun q => by simp [hP, chi]⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : P (n + 1) = Nat.xor (P n) (term A B n) := rfl
      refine ⟨by rw [e]; exact Nat.xor_lt_two_pow h1 (term_spec A B n).1, fun q => ?_⟩
      rw [e, Finset.sum_range_succ, ← h2]
      change chi ((P n ^^^ term A B n).testBit q) = _
      rw [Nat.testBit_xor, chi_xor]
  obtain ⟨k1, k2⟩ := key 27 le_rfl
  refine ⟨by rw [hm]; exact k1, fun i j hi hj => ?_⟩
  rw [hm, k2, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(term_spec A B l.val).2 i j hi hj, chi_and]

private theorem M729_eq : M729 = 2 ^ 729 - 1 := by
  change (1 <<< 729 : ℕ) - 1 = _
  rw [Nat.one_shiftLeft]

private theorem lo_bit (X q : ℕ) (hq : q < 729) : (Nat.land X M729).testBit q = X.testBit q := by
  change (X &&& M729).testBit q = _
  rw [M729_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  simp [hq]

private theorem hi_bit (X q : ℕ) : (Nat.shiftRight X 729).testBit q = X.testBit (729 + q) :=
  Nat.testBit_shiftRight X

private theorem om_sq : om ^ 2 + om + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))
  simpa [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] using h

theorem mul4_sound {X Y : ℕ} (hX : wf4 X = true) (hY : wf4 Y = true) :
    wf4 (mul4 X Y) = true ∧ dec4 (mul4 X Y) = dec4 X * dec4 Y := by
  have _hXY := And.intro hX hY
  set x0 := Nat.land X M729
  set x1 := Nat.shiftRight X 729
  set y0 := Nat.land Y M729
  set y1 := Nat.shiftRight Y 729
  set L := Nat.xor (m2 x0 y0) (m2 x1 y1)
  set H := Nat.xor (Nat.xor (m2 x0 y1) (m2 x1 y0)) (m2 x1 y1)
  have hL : L < 2 ^ 729 := Nat.xor_lt_two_pow (m2_spec _ _).1 (m2_spec _ _).1
  have hH : H < 2 ^ 729 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (m2_spec _ _).1 (m2_spec _ _).1) (m2_spec _ _).1
  have hm : mul4 X Y = L ||| H <<< 729 := rfl
  have hlo : ∀ q, q < 729 → (mul4 X Y).testBit q = L.testBit q := by
    intro q hq
    rw [hm, Nat.testBit_or, Nat.testBit_shiftLeft]
    simp [show ¬ q ≥ 729 by omega]
  have hhi : ∀ q, (mul4 X Y).testBit (729 + q) = H.testBit q := by
    intro q
    rw [hm, Nat.testBit_or, Nat.testBit_shiftLeft, bit_hi hL (by omega)]
    simp
  refine ⟨?_, ?_⟩
  · change Nat.blt (L ||| H <<< 729) (1 <<< 1458) = true
    rw [Nat.blt_eq, Nat.one_shiftLeft]
    have h1 : (2 : ℕ) ^ 729 ≤ 2 ^ 1458 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have key : ∀ x k : ℕ, x < 2 ^ k → x <<< k < 2 ^ (k + k) := fun x k hx => by
      rw [Nat.shiftLeft_eq, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos k)
    exact Nat.or_lt_two_pow (Nat.lt_of_lt_of_le hL h1) (key H 729 hH)
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hq : 27 * i.val + j.val < 729 := by omega
  simp only [dec4, Matrix.mul_apply]
  rw [bit4_eq, bit4_eq, show 729 + 27 * i.val + j.val = 729 + (27 * i.val + j.val) by ring, hlo _ hq,
    hhi]
  change chi ((m2 x0 y0 ^^^ m2 x1 y1).testBit _) + chi (((m2 x0 y1 ^^^ m2 x1 y0) ^^^ m2 x1 y1).testBit _) * om = _
  simp only [Nat.testBit_xor, chi_xor]
  rw [(m2_spec x0 y0).2 _ _ hi hj, (m2_spec x1 y1).2 _ _ hi hj, (m2_spec x0 y1).2 _ _ hi hj,
    (m2_spec x1 y0).2 _ _ hi hj]
  simp only [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl := l.isLt
  rw [lo_bit _ _ (by omega), lo_bit _ _ (by omega), hi_bit, hi_bit, bit4_eq, bit4_eq, bit4_eq, bit4_eq,
    show 729 + (27 * i.val + l.val) = 729 + 27 * i.val + l.val by ring,
    show 729 + (27 * l.val + j.val) = 729 + 27 * l.val + j.val by ring]
  set a := chi (X.testBit (27 * i.val + l.val))
  set b := chi (X.testBit (729 + 27 * i.val + l.val))
  set c := chi (Y.testBit (27 * l.val + j.val))
  set d := chi (Y.testBit (729 + 27 * l.val + j.val))
  linear_combination (-(b * d)) * om_sq + b * d * (om + 1) * two_F4

private theorem one_ne_zero_F4 : (1 : F4) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial F4 := AdjoinRoot.nontrivial _ (by
    rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)).degree = 2 by compute_degree!]
    decide)
  exact one_ne_zero

private theorem om_ne_zero : om ≠ 0 := by
  intro h
  apply one_ne_zero_F4
  linear_combination om_sq - (om + 1) * h

private theorem om_ne_one : om ≠ 1 := by
  intro h
  apply one_ne_zero_F4
  linear_combination om_sq - (om + 2) * h - two_F4

private theorem chi_pair_inj (a b c d : Bool) (h : chi a + chi b * om = chi c + chi d * om) :
    a = c ∧ b = d := by
  have h1 := one_ne_zero_F4
  have h2 := om_ne_zero
  have h3 := om_ne_one
  have h4 := two_F4
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [chi, Bool.false_eq_true, ↓reduceIte, zero_mul, one_mul, add_zero, zero_add] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd (by linear_combination h) h1
    | exact absurd (by linear_combination -h) h1
    | exact absurd (by linear_combination h) h2
    | exact absurd (by linear_combination -h) h2
    | exact absurd (by linear_combination h) h3
    | exact absurd (by linear_combination -h) h3
    | exact absurd (by linear_combination h - h4) h3
    | exact absurd (by linear_combination -h - h4) h3

private theorem wf4_lt {X : ℕ} (h : wf4 X = true) : X < 2 ^ 1458 := by
  change Nat.blt X (1 <<< 1458) = true at h
  rwa [Nat.blt_eq, Nat.one_shiftLeft] at h

theorem dec4_inj {X Y : ℕ} (hX : wf4 X = true) (hY : wf4 Y = true) (h : dec4 X = dec4 Y) : X = Y := by
  have hpair : ∀ q, q < 729 → X.testBit q = Y.testBit q ∧ X.testBit (729 + q) = Y.testBit (729 + q) := by
    intro q hq
    have hi : q / 27 < 27 := by omega
    have hj : q % 27 < 27 := Nat.mod_lt _ (by norm_num)
    have e := congrFun (congrFun h ⟨q / 27, hi⟩) ⟨q % 27, hj⟩
    simp only [dec4, bit4_eq] at e
    have eq : 27 * (q / 27) + q % 27 = q := Nat.div_add_mod q 27
    rw [show 729 + 27 * (q / 27) + q % 27 = 729 + q by omega, eq] at e
    exact chi_pair_inj _ _ _ _ e
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 729 with hq | hq
  · exact (hpair q hq).1
  rcases Nat.lt_or_ge q 1458 with hq' | hq'
  · have := (hpair (q - 729) (by omega)).2
    rwa [show 729 + (q - 729) = q by omega] at this
  · rw [bit_hi (wf4_lt hX) hq', bit_hi (wf4_lt hY) hq']

private theorem dec4_zero : dec4 0 = 0 := by
  ext i j
  simp [dec4, bit4]

private theorem dec4_one4 : dec4 one4 = 1 := by
  have hlo : ∀ i j : Fin 27, Nat.land (Nat.shiftRight one4 (27 * i.val + j.val)) 1 =
      if i = j then 1 else 0 := by decide +kernel
  have hhi : ∀ i j : Fin 27, Nat.land (Nat.shiftRight one4 (729 + 27 * i.val + j.val)) 1 = 0 := by
    decide +kernel
  ext i j
  simp only [dec4, bit4, hlo, hhi, Matrix.one_apply]
  split_ifs <;> simp

private theorem wf4_mono {X : ℕ} (h : X < 2 ^ 1458) : wf4 X = true := by
  change Nat.blt X (1 <<< 1458) = true
  rw [Nat.blt_eq, Nat.one_shiftLeft]
  exact h

private theorem mul4_zero {Y : ℕ} (hY : wf4 Y = true) : mul4 0 Y = 0 := by
  have h0 : wf4 0 = true := wf4_mono (Nat.two_pow_pos _)
  obtain ⟨hw, hd⟩ := mul4_sound h0 hY
  exact dec4_inj hw h0 (by rw [hd, dec4_zero, zero_mul])

end Mat

private def fld (i X : ℕ) : ℕ := X / 65536 ^ i % 65536

private def fsum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i * 65536 ^ i

private theorem fld_concat {A B p i : ℕ} (hA : A < 65536 ^ p) :
    fld i (A + B * 65536 ^ p) = if i < p then fld i A else fld (i - p) B := by
  unfold fld
  split_ifs with hi
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
    have e : B * 65536 ^ (i + d + 1) = 65536 ^ i * (65536 * (B * 65536 ^ d)) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + B * 65536 ^ p) / 65536 ^ (p + j) = B / 65536 ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm B, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

private theorem fsum_succ (f : ℕ → ℕ) (n : ℕ) : fsum f (n + 1) = fsum f n + f n * 65536 ^ n :=
  Finset.sum_range_succ _ _

private theorem fsum_spec (f : ℕ → ℕ) : ∀ n, (∀ i < n, f i < 65536) →
    fsum f n < 65536 ^ n ∧ ∀ i < n, fld i (fsum f n) = f i
  | 0, _ => ⟨by simp [fsum], fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hf => by
    obtain ⟨hlt, hl⟩ := fsum_spec f n fun i hi => hf i (by omega)
    have hn := hf n (by omega)
    rw [fsum_succ]
    refine ⟨?_, fun i hi => ?_⟩
    · calc fsum f n + f n * 65536 ^ n < 65536 ^ n + f n * 65536 ^ n := by omega
        _ = (f n + 1) * 65536 ^ n := by ring
        _ ≤ 65536 * 65536 ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = 65536 ^ (n + 1) := by ring
    · rw [fld_concat hlt]
      split_ifs with h
      · exact hl i h
      · have : i = n := by omega
        subst this
        simp [fld, Nat.mod_eq_of_lt hn]

private theorem fsum_fld (X : ℕ) : ∀ n, fsum (fun i => fld i X) n = X % 65536 ^ n
  | 0 => by simp [fsum, Nat.mod_one]
  | n + 1 => by
    rw [fsum_succ, fsum_fld X n, Nat.mod_pow_succ]
    unfold fld
    ring

private theorem fsum_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, f i = g i) : fsum f n = fsum g n :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

private theorem fsum_add (f g : ℕ → ℕ) (n : ℕ) : fsum f n + fsum g n = fsum (fun i => f i + g i) n := by
  unfold fsum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (add_mul _ _ _).symm

private theorem fsum_sub {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, g i ≤ f i) :
    fsum f n - fsum g n = fsum (fun i => f i - g i) n := by
  have : fsum f n = fsum (fun i => f i - g i) n + fsum g n := by
    rw [fsum_add]
    exact fsum_congr fun i hi => (Nat.sub_add_cancel (h i hi)).symm
  omega

private theorem fld_land (N q : ℕ) : Nat.land (Nat.shiftRight N (16 * q)) 65535 = fld q N := by
  change (N >>> (16 * q)) &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

private theorem decN_eq (N : ℕ) (q : Fin 7) : decN N q = (fld q.val N : ℤ) - 32768 := by
  unfold decN
  rw [fld_land]

private theorem nOK_spec {N : ℕ} (h : nOK N = true) :
    N = fsum (fun i => fld i N) 7 ∧ ∀ q < 7, 16384 ≤ fld q N ∧ fld q N < 49152 := by
  unfold nOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hN : N < 65536 ^ 7 := by
    change Nat.blt N (1 <<< 112) = true at h1
    rw [Nat.blt_eq, Nat.one_shiftLeft] at h1
    calc N < 2 ^ 112 := h1
      _ = 65536 ^ 7 := by norm_num
  refine ⟨by rw [fsum_fld, Nat.mod_eq_of_lt hN], fun q hq => ?_⟩
  have := (LceP.allRec_iff (fun k => (fun f => andB (Nat.ble (nat_lit 16384) f) (Nat.blt f (nat_lit 49152)))
    (Nat.land (Nat.shiftRight N (Nat.mul (nat_lit 16) k)) (nat_lit 65535))) 7).1 h2 q hq
  simp only [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  rw [show Nat.mul 16 q = 16 * q from rfl, fld_land] at this
  exact this

private theorem OFF_eq : fsum (fun _ => 32768) 7 = OFF := by
  have hO : OFF < 65536 ^ 7 := by decide
  have hf : ∀ i < 7, fld i OFF = 32768 := by decide
  calc fsum (fun _ => 32768) 7 = fsum (fun i => fld i OFF) 7 := fsum_congr fun i hi => (hf i hi).symm
    _ = OFF := by rw [fsum_fld, Nat.mod_eq_of_lt hO]

private theorem nOK_OFF : nOK OFF = true := by decide +kernel

private theorem decN_OFF : decN OFF = 0 := by
  funext q
  rw [decN_eq]
  have hf : ∀ i < 7, fld i OFF = 32768 := by decide
  rw [hf q.val q.isLt]
  simp

private theorem decN_add {a l : ℕ} (ha : nOK a = true) (hl : nOK l = true) :
    decN (Nat.sub (Nat.add a l) OFF) = decN a + decN l := by
  obtain ⟨ea, fa⟩ := nOK_spec ha
  obtain ⟨el, fl⟩ := nOK_spec hl
  have e : Nat.sub (Nat.add a l) OFF = fsum (fun i => fld i a + fld i l - 32768) 7 := by
    change a + l - OFF = _
    calc a + l - OFF = fsum (fun i => fld i a) 7 + fsum (fun i => fld i l) 7 - fsum (fun _ => 32768) 7 := by
          rw [← ea, ← el, OFF_eq]
      _ = fsum (fun i => fld i a + fld i l) 7 - fsum (fun _ => 32768) 7 := by rw [fsum_add]
      _ = _ := fsum_sub fun i hi => by have := fa i hi; have := fl i hi; omega
  have hlt : ∀ i < 7, fld i a + fld i l - 32768 < 65536 := fun i hi => by
    have := fa i hi
    have := fl i hi
    omega
  funext q
  rw [e, Pi.add_apply, decN_eq, decN_eq, decN_eq, (fsum_spec _ 7 hlt).2 q.val q.isLt]
  have h1 := fa q.val q.isLt
  have h2 := fl q.val q.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem decN_sub {a l : ℕ} (ha : nOK a = true) (hl : nOK l = true) :
    decN (Nat.sub (Nat.add a OFF) l) = decN a - decN l := by
  obtain ⟨ea, fa⟩ := nOK_spec ha
  obtain ⟨el, fl⟩ := nOK_spec hl
  have e : Nat.sub (Nat.add a OFF) l = fsum (fun i => fld i a + 32768 - fld i l) 7 := by
    change a + OFF - l = _
    calc a + OFF - l = fsum (fun i => fld i a) 7 + fsum (fun _ => 32768) 7 - fsum (fun i => fld i l) 7 := by
          rw [← ea, ← el, OFF_eq]
      _ = fsum (fun i => fld i a + 32768) 7 - fsum (fun i => fld i l) 7 := by rw [fsum_add]
      _ = _ := fsum_sub fun i hi => by have := fa i hi; have := fl i hi; omega
  have hlt : ∀ i < 7, fld i a + 32768 - fld i l < 65536 := fun i hi => by
    have := fa i hi
    have := fl i hi
    omega
  funext q
  rw [e, Pi.sub_apply, decN_eq, decN_eq, decN_eq, (fsum_spec _ 7 hlt).2 q.val q.isLt]
  have h1 := fa q.val q.isLt
  have h2 := fl q.val q.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem M1458_eq : M1458 = 2 ^ 1458 - 1 := by
  change (1 <<< 1458 : ℕ) - 1 = _
  rw [Nat.one_shiftLeft]

private theorem lor_shift (X Q k : ℕ) (hX : X < 2 ^ k) : X ||| Q <<< k = X + 2 ^ k * Q := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hX, Nat.add_comm]

private theorem mkA_eq {X p N : ℕ} (hX : X < 2 ^ 1458) (hp : p < 2) :
    mkA X p N = X + 2 ^ 1458 * (p + 2 * N) := by
  change X ||| (p <<< 1458 ||| N <<< 1459) = _
  have e1 : N <<< 1459 = (N <<< 1) <<< 1458 := Nat.shiftLeft_add N 1 1458
  rw [e1, ← Nat.shiftLeft_or_distrib, lor_shift p N 1 (by simpa using hp), lor_shift X _ 1458 hX,
    pow_one]

private theorem aX_mkA {X p N : ℕ} (hX : X < 2 ^ 1458) (hp : p < 2) : aX (mkA X p N) = X := by
  change mkA X p N &&& M1458 = X
  rw [M1458_eq, Nat.and_two_pow_sub_one_eq_mod, mkA_eq hX hp, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hX]

private theorem div_mkA {X p N : ℕ} (hX : X < 2 ^ 1458) (hp : p < 2) :
    mkA X p N / 2 ^ 1458 = p + 2 * N := by
  rw [mkA_eq hX hp, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hX, zero_add]

private theorem aP_mkA {X p N : ℕ} (hX : X < 2 ^ 1458) (hp : p < 2) : aP (mkA X p N) = p := by
  change (mkA X p N >>> 1458) &&& 1 = p
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, div_mkA hX hp]
  omega

private theorem aN_mkA {X p N : ℕ} (hX : X < 2 ^ 1458) (hp : p < 2) : aN (mkA X p N) = N := by
  change mkA X p N >>> 1459 = N
  rw [Nat.shiftRight_eq_div_pow, pow_succ, ← Nat.div_div_eq_div_mul, div_mkA hX hp]
  omega

private theorem aX_lt (A : ℕ) : aX A < 2 ^ 1458 := by
  change A &&& M1458 < _
  rw [M1458_eq]
  exact Nat.and_lt_two_pow _ (by omega)

private theorem lX_lt (A : ℕ) : lX A < 2 ^ 1458 := by
  change A &&& M1458 < _
  rw [M1458_eq]
  exact Nat.and_lt_two_pow _ (by omega)

private theorem lXI_lt (A : ℕ) : lXI A < 2 ^ 1458 := by
  change (A >>> 1458) &&& M1458 < _
  rw [M1458_eq]
  exact Nat.and_lt_two_pow _ (by omega)

private theorem aP_lt (A : ℕ) : aP A < 2 := by
  change (A >>> 1458) &&& 1 < 2
  rw [Nat.and_one_is_mod]
  omega

private theorem lP_lt (A : ℕ) : lP A < 2 := by
  change (A >>> 2916) &&& 1 < 2
  rw [Nat.and_one_is_mod]
  omega

private theorem aX_zero : aX 0 = 0 := rfl

private noncomputable def d2 (X : ℕ) : Multiplicative (ZMod 2) := Multiplicative.ofAdd (X : ZMod 2)

private theorem d2_xor {a b : ℕ} (ha : a < 2) (hb : b < 2) : d2 (Nat.xor a b) = d2 a * d2 b := by
  interval_cases a <;> interval_cases b <;> decide

private theorem d2_sq (a : ℕ) : d2 a * d2 a = 1 := by
  unfold d2
  rw [← ofAdd_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, ofAdd_zero]

abbrev Tg : Type := Matrix (Fin 27) (Fin 27) F4 × Multiplicative (ZMod 2) × Multiplicative (Fin 7 → ℤ)

private noncomputable def DA (A : ℕ) : Tg := (dec4 (aX A), d2 (aP A), Multiplicative.ofAdd (decN (aN A)))

private noncomputable def DL (L : ℕ) : Tg := (dec4 (lX L), d2 (lP L), Multiplicative.ofAdd (decN (lN L)))

private noncomputable def DLi (L : ℕ) : Tg :=
  (dec4 (lXI L), d2 (lP L), Multiplicative.ofAdd (-decN (lN L)))

private theorem push_cases (L dir A : ℕ) :
    pushL L dir A = 0 ∨ (nOK (lN L) = true ∧
      nOK (aN (Bool.rec (motive := fun _ => ℕ)
        (mkA (mul4 (aX A) (lX L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) (lN L)) OFF))
        (mkA (mul4 (aX A) (lXI L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) OFF) (lN L)))
        (Nat.beq dir (nat_lit 1)))) = true ∧
      pushL L dir A = Bool.rec (motive := fun _ => ℕ)
        (mkA (mul4 (aX A) (lX L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) (lN L)) OFF))
        (mkA (mul4 (aX A) (lXI L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) OFF) (lN L)))
        (Nat.beq dir (nat_lit 1))) := by
  unfold pushL
  rw [Co2Kill.strictN_eq]
  dsimp only
  cases h : andB (nOK (lN L)) (nOK (aN (Bool.rec (motive := fun _ => ℕ)
      (mkA (mul4 (aX A) (lX L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) (lN L)) OFF))
      (mkA (mul4 (aX A) (lXI L)) (Nat.xor (aP A) (lP L)) (Nat.sub (Nat.add (aN A) OFF) (lN L)))
      (Nat.beq dir (nat_lit 1)))))
  · exact Or.inl rfl
  · rw [andB_eq, Bool.and_eq_true] at h
    exact Or.inr ⟨h.1, h.2, rfl⟩

private theorem xor_lt2 (A L : ℕ) : Nat.xor (aP A) (lP L) < 2 := by
  have := Nat.xor_lt_two_pow (n := 1) (by simpa using aP_lt A) (by simpa using lP_lt L)
  simpa using this

private theorem mul4_wf {X Y : ℕ} (hX : X < 2 ^ 1458) (hY : Y < 2 ^ 1458) : mul4 X Y < 2 ^ 1458 :=
  wf4_lt (mul4_sound (wf4_mono hX) (wf4_mono hY)).1

private theorem push_dead {L dir A : ℕ} (h : aX A = 0) : aX (pushL L dir A) = 0 := by
  rcases push_cases L dir A with h0 | ⟨-, -, e⟩
  · rw [h0]
    rfl
  rw [e, h]
  cases Nat.beq dir 1
  · dsimp only
    rw [mul4_zero (wf4_mono (lX_lt L)), aX_mkA (Nat.two_pow_pos _) (xor_lt2 A L)]
  · dsimp only
    rw [mul4_zero (wf4_mono (lXI_lt L)), aX_mkA (Nat.two_pow_pos _) (xor_lt2 A L)]

private theorem push_live {L dir A : ℕ} (hA : nOK (aN A) = true) (h : aX (pushL L dir A) ≠ 0) :
    nOK (aN (pushL L dir A)) = true ∧
      DA (pushL L dir A) = DA A * Bool.rec (motive := fun _ => Tg) (DL L) (DLi L) (Nat.beq dir 1) := by
  rcases push_cases L dir A with h0 | ⟨hL, hB, e⟩
  · rw [h0] at h
    exact absurd rfl h
  rw [e]
  refine ⟨hB, ?_⟩
  cases Nat.beq dir 1
  · dsimp only
    have hm := mul4_wf (aX_lt A) (lX_lt L)
    unfold DA DL
    rw [aX_mkA hm (xor_lt2 A L), aP_mkA hm (xor_lt2 A L), aN_mkA hm (xor_lt2 A L),
      (mul4_sound (wf4_mono (aX_lt A)) (wf4_mono (lX_lt L))).2, d2_xor (aP_lt A) (lP_lt L),
      decN_add hA hL, ofAdd_add]
    rfl
  · dsimp only
    have hm := mul4_wf (aX_lt A) (lXI_lt L)
    unfold DA DLi
    rw [aX_mkA hm (xor_lt2 A L), aP_mkA hm (xor_lt2 A L), aN_mkA hm (xor_lt2 A L),
      (mul4_sound (wf4_mono (aX_lt A)) (wf4_mono (lXI_lt L))).2, d2_xor (aP_lt A) (lP_lt L),
      decN_sub hA hL, sub_eq_add_neg, ofAdd_add]
    rfl

private theorem DA_accOne : DA accOne = 1 := by
  have h1 : one4 < 2 ^ 1458 := by decide +kernel
  unfold DA accOne
  rw [aX_mkA h1 (by norm_num), aP_mkA h1 (by norm_num), aN_mkA h1 (by norm_num), dec4_one4, decN_OFF]
  rfl

private theorem nOK_accOne : nOK (aN accOne) = true := by
  have h1 : one4 < 2 ^ 1458 := by decide +kernel
  unfold accOne
  rw [aN_mkA h1 (by norm_num)]
  exact nOK_OFF

private theorem aX_accOne : aX accOne ≠ 0 := by
  have h1 : one4 < 2 ^ 1458 := by decide +kernel
  unfold accOne
  rw [aX_mkA h1 (by norm_num)]
  decide +kernel

private theorem DA_accOf (L : ℕ) : DA (accOf L) = DL L := by
  unfold DA DL accOf
  rw [aX_mkA (lX_lt L) (lP_lt L), aP_mkA (lX_lt L) (lP_lt L), aN_mkA (lX_lt L) (lP_lt L)]

private theorem DL_labOne : DL labOne = 1 := by
  have e1 : lX labOne = one4 := by decide +kernel
  have e2 : lP labOne = 0 := by decide +kernel
  have e3 : lN labOne = OFF := by decide +kernel
  unfold DL
  rw [e1, e2, e3, dec4_one4, decN_OFF]
  rfl

private theorem DLi_labOne : DLi labOne = 1 := by
  have e1 : lXI labOne = one4 := by decide +kernel
  have e2 : lP labOne = 0 := by decide +kernel
  have e3 : lN labOne = OFF := by decide +kernel
  unfold DLi
  rw [e1, e2, e3, dec4_one4, decN_OFF, neg_zero]
  rfl

private theorem DL_DLi {L : ℕ} (h : mul4 (lX L) (lXI L) = one4) : DL L * DLi L = 1 := by
  have hd := (mul4_sound (wf4_mono (lX_lt L)) (wf4_mono (lXI_lt L))).2
  rw [h, dec4_one4] at hd
  unfold DL DLi
  refine Prod.ext hd.symm (Prod.ext (d2_sq _) ?_)
  change Multiplicative.ofAdd (decN (lN L)) * Multiplicative.ofAdd (-decN (lN L)) = 1
  rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]

private noncomputable def jList (WT : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, J => J :: jList WT k (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight J (nat_lit 1))
      (Nat.shiftRight J (jLen J (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))

private noncomputable def wOf (WT : ℕ → ℕ) (J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
    (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def jAll (WT : ℕ → ℕ) (Cs : List ℕ) : List ℕ :=
  Cs.flatMap fun C => jList WT (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8))

private theorem chunkRec_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ k J S,
    LceP.chunkRec blk WT INV nC L k J S =
      (jList WT k J).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (nat_lit 1))
        (factStep blk INV nC L J S (fct blk (sI S)) (nat_lit 0)))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
          (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact chunkRec_eq blk WT INV nC L k _ _

private theorem runFacts_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ Cs S,
    runFacts blk WT INV nC L Cs S =
      (jAll WT Cs).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (LceP.chunkRec blk WT INV nC L (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runFacts blk WT INV nC L Cs) = _
    rw [LceP.strictN_eq, runFacts_eq blk WT INV nC L Cs, chunkRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def labRec (WT LB LETs : ℕ → ℕ) (Hs : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT) (fun w =>
        CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem labRec_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ k J S,
    labRec WT LB LETs Hs k J S =
      (jList WT k J).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0))
        (labRec WT LB LETs Hs k (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w)
          (labRec WT LB LETs Hs k (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact labRec_eq WT LB LETs Hs k _ _

private theorem runLab_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ Cs S,
    runLab WT LB LETs Hs Cs S = (jAll WT Cs).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (labRec WT LB LETs Hs (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runLab WT LB LETs Hs Cs) = _
    rw [LceP.strictN_eq, runLab_eq WT LB LETs Hs Cs, labRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def idsF (m I J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) I
    (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) I
      (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def idsRec (WT : ℕ → ℕ) (m : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w =>
          ih (Nat.shiftRight J (jLen J w))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem idsRec_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ k J S,
    idsRec WT m k J S = (jList WT k J).foldl (idsF m) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ) (idsRec WT m k (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w => idsRec WT m k (Nat.shiftRight J (jLen J w))
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, idsF, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact idsRec_eq WT m k _ _

private theorem runIds_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ Cs S,
    CFSG.KC.LceSR.runIds WT m Cs S = (jAll WT Cs).foldl (idsF m) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (idsRec WT m (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (CFSG.KC.LceSR.runIds WT m Cs) = _
    rw [LceP.strictN_eq, runIds_eq WT m Cs, idsRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private theorem sF_cases (R st : ℕ) :
    sF R st = 0 ∨ (st % 268435456 = fxc R ∧ sF R st = fy R + st / 268435456 * 1048576) := by
  rw [LceP.sF_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem sB_cases (R st : ℕ) :
    sB R st = 0 ∨ (st % 268435456 = fyic R ∧ sB R st = fx R + st / 268435456 * 1048576) := by
  rw [LceP.sB_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem fwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fxc R) :
    cur = fx R ∧ wLet W p = fc R ∧
      fy R + st / 268435456 * 1048576 = fy R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fxc_eq] at hm
  have hfx := LceP.fx_lt R
  have hfc := LceP.fc_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem bwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fyic R)
    (hic : fic R < 256) :
    cur = fy R ∧ wLet W p = fic R ∧
      fx R + st / 268435456 * 1048576 = fx R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fyic_eq] at hm
  have hfy := LceP.fy_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

section Lab

variable {G L : Type*} [Group G] [Group L] (gen : ℕ → G) (π : L →* G) (Ψ : L →* Tg)

private noncomputable def LabHolds (rep : ℕ → G) (R La : ℕ) : Prop :=
  ∃ l : L, π l = LceP.el gen rep R ∧ Ψ l = DL La ∧ Ψ l⁻¹ = DLi La

private noncomputable def LRefs (blk LB : ℕ → ℕ) (INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, recOK INV nC (fct blk h) = true ∧ LabHolds gen π Ψ rep (fct blk h) (LB h)

private noncomputable def LP (rep : ℕ → G) (s W ft : ℕ) (u : G) (M : Tg) (p cur acc : ℕ) : Prop :=
  aX acc = 0 ∨ (nOK (aN acc) = true ∧
    ((p ≤ ft ∧ ∃ a : L, π a = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧ Ψ a = DA acc) ∨
      (ft < p ∧ ∃ a b : L, π a * u * π b = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        Ψ a * M * Ψ b = DA acc)))

private noncomputable def WL (rep : ℕ → G) (s W ft : ℕ) (u : G) (M : Tg) (p st acc : ℕ) : Prop :=
  st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧
    LP gen π Ψ rep s W ft u M p cur acc

private theorem WL_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (M : Tg)
    (hs : s < 1048576) : WL gen π Ψ rep s W ft u M 0 (wStart s W) accOne := by
  right
  refine ⟨s, hs, ?_, Or.inr ⟨nOK_accOne, Or.inl ⟨Nat.zero_le _, 1, ?_, ?_⟩⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [map_one, LceP.bv_zero, mul_one, mul_inv_cancel]
  · rw [map_one, DA_accOne]

private theorem LP_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Tg}
    {p acc acc' cur cur' : ℕ} {c : L} {Mc : Tg} (hp : p ≠ ft)
    (hX : LP gen π Ψ rep s W ft u M p cur acc)
    (hc : π c = rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) (hcM : Ψ c = Mc)
    (hdead : aX acc = 0 → aX acc' = 0)
    (hlive : nOK (aN acc) = true → aX acc' ≠ 0 → nOK (aN acc') = true ∧ DA acc' = DA acc * Mc) :
    LP gen π Ψ rep s W ft u M (p + 1) cur' acc' := by
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  rcases hX with h0 | ⟨hN, hX⟩
  · exact Or.inl (hdead h0)
  by_cases h0 : aX acc' = 0
  · exact Or.inl h0
  obtain ⟨hN', hd⟩ := hlive hN h0
  refine Or.inr ⟨hN', ?_⟩
  rcases hX with ⟨hp', a, ha, haψ⟩ | ⟨hp', a, b, hab, habψ⟩
  · refine Or.inl ⟨by omega, a * c, ?_, ?_⟩
    · rw [map_mul, ha, hc, e]
    · rw [map_mul, haψ, hcM, hd]
  · refine Or.inr ⟨by omega, a, b * c, ?_, ?_⟩
    · rw [map_mul, e, ← hab, hc]
      group
    · rw [map_mul, hd, ← habψ, hcM]
      simp only [mul_assoc]

private theorem WL_ref {blk LB : ℕ → ℕ} {INV INV8 Lc nC i : ℕ} (hinv : invOK INV INV8 Lc = true)
    {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Tg} {p st acc : ℕ}
    (e : ℕ) (hrefs : LRefs gen π Ψ blk LB INV nC rep i) (hp : p ≠ ft)
    (hI : WL gen π Ψ rep s W ft u M p st acc) :
    WL gen π Ψ rep s W ft u M (p + 1) (refStep blk i e st)
      (pushL (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc) := by
  unfold refStep
  rw [LceP.brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [LceP.strictN_eq]
    obtain ⟨hrec, l, hl, hlX, hlXI⟩ := hrefs _ hh
    set R := fct blk (Nat.shiftRight e (nat_lit 1))
    have hlv := (LceP.lv_fic gen blk hinv hrec).1
    have hlive := fun hN h0 => push_live (L := LB (Nat.shiftRight e (nat_lit 1)))
      (dir := Nat.land e (nat_lit 1)) (A := acc) hN h0
    have hdead := fun h0 => push_dead (L := LB (Nat.shiftRight e (nat_lit 1)))
      (dir := Nat.land e (nat_lit 1)) (A := acc) h0
    rw [LceP.brec_eq]
    split_ifs with hd
    ·
      rw [hd] at hlive
      rcases hI with hdead' | ⟨cur, hcur, hst, hX⟩
      · left
        rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fx_lt R
          omega
      · rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := bwd_arith hcur hst hm (LceP.fic_lt blk _)
          refine ⟨fx R, LceP.fx_lt R, by rw [h1, hs], ?_⟩
          refine LP_ext gen π Ψ hp hX (c := l⁻¹) ?_ hlXI hdead hlive
          have hlv' : LceP.lv gen (fic R) = (LceP.lv gen (fc R))⁻¹ := hlv
          rw [map_inv, hl, hw, hlv', hc]
          unfold LceP.el
          group
    ·
      have hd' : Nat.beq (Nat.land e (nat_lit 1)) 1 = false := by
        cases h : Nat.beq (Nat.land e (nat_lit 1)) 1
        · rfl
        · exact absurd h hd
      rw [hd'] at hlive
      rcases hI with hdead' | ⟨cur, hcur, hst, hX⟩
      · left
        rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fy_lt R
          omega
      · rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
          refine ⟨fy R, LceP.fy_lt R, by rw [h1, hs], ?_⟩
          refine LP_ext gen π Ψ hp hX (c := l) ?_ hlX hdead hlive
          rw [hl, hw, hc]
          rfl
  · left
    rfl

private theorem WL_own {rep : ℕ → G} {s W ft Ri Li p st acc : ℕ} (hp : p = ft)
    (hI : WL gen π Ψ rep s W ft (LceP.el gen rep Ri) (DL Li) p st acc) :
    WL gen π Ψ rep s W ft (LceP.el gen rep Ri) (DL Li) (p + 1) (sF Ri st) (pushL Li (nat_lit 0) acc) := by
  rcases hI with hdead | ⟨cur, hcur, hst, hX⟩
  · left
    rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · rw [h0]
    · rw [h1]
      have := LceP.fy_lt Ri
      omega
  · rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · left
      rw [h0]
    · right
      obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
      refine ⟨fy Ri, LceP.fy_lt Ri, by rw [h1, hs], ?_⟩
      rcases hX with h0 | ⟨hN, hX⟩
      · exact Or.inl (push_dead h0)
      by_cases h0 : aX (pushL Li 0 acc) = 0
      · exact Or.inl h0
      obtain ⟨hN', hd⟩ := push_live hN h0
      refine Or.inr ⟨hN', Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩
      · refine ⟨a, 1, ?_, ?_⟩
        · rw [map_one, mul_one, ha, LceP.bv_succ, hw, hc]
          unfold LceP.el
          group
        · rw [map_one, mul_one, haψ, hd]
          rfl
      · omega

private theorem walk_lab {blk LB : ℕ → ℕ} {INV INV8 Lc nC i : ℕ} (hinv : invOK INV INV8 Lc = true)
    {rep : ℕ → G} {s W Ri Li ft n : ℕ} (hrefs : LRefs gen π Ψ blk LB INV nC rep i) :
    ∀ k ≤ n, ∀ J st acc,
      WL gen π Ψ rep s W ft (LceP.el gen rep Ri) (DL Li) (n - k) st acc →
      WL gen π Ψ rep s W ft (LceP.el gen rep Ri) (DL Li) n
        (walkGo blk i Ri ft n k J st) (labGo LB Li ft n k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π Ψ rep s W ft (LceP.el gen rep Ri) (DL Li) n
      (Bool.rec (motive := fun _ => ℕ)
        (walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st))
        (walkGo blk i Ri ft n k J (sF Ri st)) (Nat.beq (Nat.sub n (Nat.succ k)) ft))
      (Bool.rec (motive := fun _ => ℕ)
        ((fun e => CFSG.KC.Loop.strictN (pushL (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc)
            (labGo LB Li ft n k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
        (CFSG.KC.Loop.strictN (pushL Li 0 acc) (labGo LB Li ft n k J))
        (Nat.beq (Nat.sub n (Nat.succ k)) ft))
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs k (by omega)
      rw [e]
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      exact WL_ref gen π Ψ hinv _ hrefs hp hI
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs k (by omega)
      rw [e]
      exact WL_own gen π Ψ (Nat.eq_of_beq_eq_true hb) hI

private theorem walk_cyc {blk LB : ℕ → ℕ} {INV INV8 Lc nC i : ℕ} (hinv : invOK INV INV8 Lc = true)
    {rep : ℕ → G} {s W n : ℕ} {u : G} {M : Tg}
    (hrefs : LRefs gen π Ψ blk LB INV nC rep i) :
    ∀ k ≤ n, ∀ J st acc, WL gen π Ψ rep s W n u M (n - k) st acc →
      WL gen π Ψ rep s W n u M n (cycWalk blk i k J st) (cycLab LB k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π Ψ rep s W n u M n
      (CFSG.KC.Loop.strictN (refStep blk i (Nat.land J 4294967295) st)
        (cycWalk blk i k (Nat.shiftRight J 32)))
      ((fun e => CFSG.KC.Loop.strictN (pushL (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc)
        (cycLab LB k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
    dsimp only
    rw [LceP.strictN_eq, LceP.strictN_eq]
    apply walk_cyc hinv hrefs k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_ref gen π Ψ hinv _ hrefs (by omega) hI

private noncomputable def LInv (blk LB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
    LRefs gen π Ψ blk LB INV nC rep' i

private noncomputable def LGood (blk LB : ℕ → ℕ) (INV nC S T I : ℕ) : Prop :=
  S = 0 ∨ T = 0 ∨ I = 0 ∨ 4294967296 < T ∨
    (1 ≤ sN S ∧ T = sI S + 1 ∧ LInv gen π Ψ blk LB INV nC (sI S) (sN S))

private theorem lab_of_walk {u : G} {M Q : Tg} {a b t : L}
    (hab : π a * u * π b = π t) (hψ : Ψ a * M * Ψ b = Ψ t) (hMQ : M * Q = 1) :
    ∃ l : L, π l = u ∧ Ψ l = M ∧ Ψ l⁻¹ = Q := by
  have hM : Ψ (a⁻¹ * t * b⁻¹) = M := by
    rw [map_mul, map_mul, ← hψ]
    calc Ψ a⁻¹ * (Ψ a * M * Ψ b) * Ψ b⁻¹ = (Ψ a⁻¹ * Ψ a) * M * (Ψ b * Ψ b⁻¹) := by
          simp only [mul_assoc]
      _ = M := by rw [← map_mul, ← map_mul, inv_mul_cancel, mul_inv_cancel, map_one, one_mul, mul_one]
  refine ⟨a⁻¹ * t * b⁻¹, ?_, hM, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, ← hab]
    group
  · calc Ψ (a⁻¹ * t * b⁻¹)⁻¹ = Ψ (a⁻¹ * t * b⁻¹)⁻¹ * (M * Q) := by rw [hMQ, mul_one]
      _ = Q := by rw [← hM, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem labStep_cases (LB LETs : ℕ → ℕ) (Hs J T w : ℕ) :
    labStep LB LETs Hs J T w = 0 ∨ labStep LB LETs Hs J T w = T + 1 := by
  unfold labStep
  cases Nat.blt (nat_lit 0) T
  · exact Or.inl rfl
  · dsimp only
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> dsimp only
    · cases Nat.beq (LB (Nat.sub T (nat_lit 1))) labOne
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases labWalk LB LETs (Nat.sub T (nat_lit 1)) J w
        (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem LGood_step {blk WT ST LB LETs : ℕ → ℕ} {INV INV8 Lc nC m Hs K : ℕ}
    (hinv : invOK INV INV8 Lc = true)
    (hW2 : ∀ id < m, wKind (WT id) = 2 → LceP.bv gen (wWord (WT id)) (wLen (WT id)) = 1)
    (hW3 : ∀ id < m, wKind (WT id) = 3 → hint Hs id < K ∧
      LceP.bv gen (wWord (WT id)) (wLen (WT id)) =
        LceP.bv gen (wWord (ST (hint Hs id))) (wLen (ST (hint Hs id))))
    (hLET : ∀ j < K, lX (LETs j) ≠ 0 ∧ ∃ t : L,
      π t = LceP.bv gen (wWord (ST j)) (wLen (ST j)) ∧ Ψ t = DL (LETs j))
    {S T I : ℕ} (J : ℕ) (hG : LGood gen π Ψ blk LB INV nC S T I) :
    LGood gen π Ψ blk LB INV nC (factStep blk INV nC Lc J S (fct blk (sI S)) (wOf WT J))
      (labStep LB LETs Hs J T (wOf WT J)) (idsF m I J) := by
  rcases hG with h0 | h0 | h0 | h0 | ⟨hN, hT, rep, hrep0, hrefs⟩
  · left
    rw [h0]
    rfl
  · right; left
    rw [h0]
    rfl
  · right; right; left
    rw [h0]
    unfold idsF
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;>
      cases Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m <;> rfl
  · rcases labStep_cases LB LETs Hs J T (wOf WT J) with h | h
    · right; left
      exact h
    · right; right; right; left
      rw [h]
      omega
  set i := sI S with hidef
  set N := sN S with hNdef
  have hi32 : i < 4294967296 := LceP.sI_lt S
  have hS0 : Nat.blt (nat_lit 0) S = true := by
    rw [Nat.blt_eq]
    change 0 < S
    have : S / 4294967296 ≥ 1 := by rw [← LceP.sN_eq]; exact hN
    omega
  have hT0 : Nat.blt (nat_lit 0) T = true := by
    rw [Nat.blt_eq]
    change 0 < T
    omega
  have hT1 : Nat.sub T (nat_lit 1) = i := by
    change T - 1 = i
    omega
  have hnext : ∀ N' : ℕ, 1 ≤ N' → LInv gen π Ψ blk LB INV nC (i + 1) N' → ∀ I' : ℕ,
      LGood gen π Ψ blk LB INV nC (mkS (Nat.succ i) N') (T + 1) I' := by
    intro N' hN' hL I'
    rcases Nat.lt_or_ge (i + 1) 4294967296 with hlt | hge
    · right; right; right; right
      have e1 : sI (mkS (Nat.succ i) N') = i + 1 := by
        rw [LceP.sI_eq, LceP.mkS_eq N' hlt]
        omega
      have e2 : sN (mkS (Nat.succ i) N') = N' := by
        rw [LceP.sN_eq, LceP.mkS_eq N' hlt]
        omega
      rw [e1, e2]
      exact ⟨hN', by omega, hL⟩
    · right; right; right; left
      omega
  unfold factStep labStep idsF wOf
  rw [hS0, hT0, hT1]
  dsimp only
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases hft : fTree INV nC Lc (fct blk i) N
    · left
      rfl
    cases hlb : Nat.beq (LB i) labOne
    · right; left
      rfl
    dsimp only
    refine hnext (N + 1) (by omega) ?_ _
    unfold fTree at hft
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at hft
    obtain ⟨hrR, hfy, hfx, -⟩ := hft
    have hLB : LB i = labOne := Nat.eq_of_beq_eq_true hlb
    set R := fct blk i
    refine ⟨Function.update rep N (rep (fx R) * LceP.lv gen (fc R)), ?_, fun rep' hag h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' h hh
    · refine ⟨hrR, 1, ?_, ?_, ?_⟩
      · rw [map_one]
        unfold LceP.el
        rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel]
      · rw [map_one, hLB, DL_labOne]
      · rw [inv_one, map_one, hLB, DLi_labOne]
  ·
    dsimp only
    set id := Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535) with hiddef
    cases hid : Nat.blt id m
    · right; right; left
      rfl
    have hidm : id < m := LceP.blt_true hid
    set w := WT id
    set fs := Nat.land (Nat.shiftRight J (nat_lit 17)) (nat_lit 1048575)
    set ft := Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)
    cases hwk : walkOK blk INV nC i (fct blk i) w fs ft J
    · left
      rfl
    cases hlw : labWalk LB LETs i J w (hint Hs id)
    · right; left
      rfl
    dsimp only
    set R := fct blk i
    refine hnext N hN ⟨rep, hrep0, fun rep' hag h hh => ?_⟩ _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag h hh
    unfold walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hwalk⟩ := hwk
    unfold labWalk at hlw
    rw [LceP.letB_eq] at hlw
    simp only [LceP.andB_iff, Nat.beq_eq] at hlw
    obtain ⟨hmul, hlab⟩ := hlw
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag
    have hstart := WL_start gen π Ψ rep' (wWord w) ft (LceP.el gen rep' R) (DL (LB i)) hfs
    have hW := walk_lab gen π Ψ hinv hrefs' (wLen w) le_rfl (Nat.shiftRight J 53) _ _
      (by rw [Nat.sub_self]; exact hstart)
    rw [hwalk, hlab] at hW
    refine ⟨hrec, ?_⟩
    rcases hW with hdead | ⟨cur, hcur, hst, hX⟩
    · exfalso
      omega
    have hW1 : wWord w / 256 ^ wLen w = 1 := by omega
    have hc : cur = fs := by omega
    rw [hc] at hX
    have htX : aX (target LETs w (hint Hs id)) ≠ 0 := by
      unfold target
      cases hk : Nat.beq (wKind w) (nat_lit 3)
      · exact aX_accOne
      · have hk3 : wKind w = 3 := Nat.eq_of_beq_eq_true hk
        dsimp only
        unfold accOf
        rw [aX_mkA (lX_lt _) (lP_lt _)]
        exact (hLET _ (hW3 id hidm hk3).1).1
    rcases hX with h0 | ⟨-, hX⟩
    · exact absurd h0 htX
    rcases hX with ⟨hle, -⟩ | ⟨-, a, b, hab, habψ⟩
    · exfalso
      omega
    rcases hkind with hk2 | ⟨hk3, hfs0⟩
    ·
      have hbv := hW2 id hidm hk2
      have htg : target LETs w (hint Hs id) = accOne := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = false by rw [hk2]; rfl]
      rw [htg, DA_accOne] at habψ
      refine lab_of_walk π Ψ (a := a) (b := b) (t := 1) ?_ ?_ (DL_DLi hmul)
      · rw [hab, hbv, mul_one, mul_inv_cancel, map_one]
      · rw [habψ, map_one]
    ·
      obtain ⟨hK, hbv⟩ := hW3 id hidm hk3
      obtain ⟨t, ht, htψ⟩ := (hLET _ hK).2
      have htg : target LETs w (hint Hs id) = accOf (LETs (hint Hs id)) := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = true by rw [hk3]; rfl]
      rw [htg, DA_accOf, ← htψ] at habψ
      have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
      refine lab_of_walk π Ψ (a := a) (b := b) ?_ habψ (DL_DLi hmul)
      rw [hab, hfs0, h0, one_mul, inv_one, mul_one, hbv, ht]

end Lab

theorem lab_sound {G L : Type*} [Group G] [Group L] (gen : ℕ → G) (π : L →* G)
    (ψ : L →* (Matrix (Fin 27) (Fin 27) F4)ˣ) (par : L →* Multiplicative (ZMod 2))
    (nv : L →* Multiplicative (Fin 7 → ℤ))
    {blk WT RT ST LB LETs : ℕ → ℕ} {INV INV8 Lc nC nf m Hs K S0 S1 T0 T1 : ℕ} {Cs : List ℕ}
    (h : coneOk blk WT RT ST LB LETs INV INV8 Lc nC nf m Hs K S0 S1 T0 T1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hLET : ∀ j < K, nOK (lN (LETs j)) = true ∧ ∃ t : L,
      π t = bval gen (wWord (ST j)) (wLen (ST j)) ∧
      ((ψ t : (Matrix (Fin 27) (Fin 27) F4)ˣ) : Matrix (Fin 27) (Fin 27) F4) = dec4 (lX (LETs j)) ∧
      par t = Multiplicative.ofAdd ((lP (LETs j) : ℕ) : ZMod 2) ∧
      nv t = Multiplicative.ofAdd (decN (lN (LETs j))))
    {nf' c wid R V : ℕ} (hnf : nf' = nf) (hc : c < 2 ^ 20) (hcyc : cycOK blk WT LB nf' c wid R V = true)
    (hVX : Nat.blt (nat_lit 0) (aX V) = true) (hVN : nOK (aN V) = true)
    (hwid : wid < m := by decide) :
    ∃ ν : L, π ν = 1 ∧
      ((ψ ν : (Matrix (Fin 27) (Fin 27) F4)ˣ) : Matrix (Fin 27) (Fin 27) F4) = dec4 (aX V) ∧
      par ν = Multiplicative.ofAdd ((aP V : ℕ) : ZMod 2) ∧ nv ν = Multiplicative.ofAdd (decN (aN V)) := by
  have _hVN := hVN
  subst nf'
  set Ψ : L →* Tg := ((Units.coeHom _).comp ψ).prod (par.prod nv) with hΨ
  have hNt : Nontrivial F4 := ⟨⟨1, 0, one_ne_zero_F4⟩⟩
  have hLET' : ∀ j < K, lX (LETs j) ≠ 0 ∧ ∃ t : L,
      π t = LceP.bv gen (wWord (ST j)) (wLen (ST j)) ∧ Ψ t = DL (LETs j) := by
    intro j hj
    obtain ⟨-, t, ht, h1, h2, h3⟩ := hLET j hj
    refine ⟨fun h0 => (ψ t).ne_zero (by rw [h1, h0, dec4_zero]), t, ht, ?_⟩
    exact Prod.ext h1 (Prod.ext h2 h3)
  unfold coneOk at h
  obtain ⟨hwords, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hrun, hlab⟩ := (LceP.andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := LceP.blt_true hnf
  have hw : ∀ j < m, (wKind (WT j) = 2 → LceP.bv gen (wWord (WT j)) (wLen (WT j)) = 1) ∧
      (wKind (WT j) = 3 → hint Hs j < K ∧ LceP.bv gen (wWord (WT j)) (wLen (WT j)) =
        LceP.bv gen (wWord (ST (hint Hs j))) (wLen (ST (hint Hs j)))) := by
    intro j hj
    have hl := LceP.hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords j hj
    rw [Nat.sub_self, Nat.zero_add] at hl
    obtain ⟨hw2, hw3⟩ := LceP.word_check hl
    have hlt := (LceP.allRec_iff (fun k => Bool.rec (motive := fun _ => Bool) true
      (Nat.blt (hint Hs k) K) (Nat.beq (wKind (WT k)) (nat_lit 3))) m).1 hhints j hj
    refine ⟨fun hk => LceP.wRel_sound gen hinv (hw2 hk) (hRT _).1 (hRT _).2, fun hk => ⟨?_, ?_⟩⟩
    · have hb : Nat.beq (wKind (WT j)) (nat_lit 3) = true := by rw [hk]; rfl
      rw [hb] at hlt
      exact LceP.blt_true hlt
    · exact LceP.wSub_sound gen (hw3 hk)
  have hstep := fun (J : ℕ) {S T I : ℕ} => LGood_step gen π Ψ (blk := blk) (WT := WT) (ST := ST)
    (LB := LB) (LETs := LETs) (Lc := Lc) (nC := nC) (m := m) (Hs := Hs) (K := K) (S := S) (T := T)
    (I := I) hinv (fun id hid => (hw id hid).1) (fun id hid => (hw id hid).2) hLET' J
  have hfold : ∀ (l : List ℕ) (S T I : ℕ), LGood gen π Ψ blk LB INV nC S T I →
      LGood gen π Ψ blk LB INV nC
        (l.foldl (fun S J => factStep blk INV nC Lc J S (fct blk (sI S)) (wOf WT J)) S)
        (l.foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) T) (l.foldl (idsF m) I) := by
    intro l
    induction l with
    | nil => intro S T I hG; exact hG
    | cons J l ih =>
      intro S T I hG
      simp only [List.foldl_cons]
      exact ih _ _ _ (hstep J hG)
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hT0' : T0 = 1 := Nat.eq_of_beq_eq_true hT0
  have hG0 : LGood gen π Ψ blk LB INV nC S0 T0 1 := by
    right; right; right; right
    have e1 : sI S0 = 0 := by rw [hS0', LceP.sI_eq, LceP.mkS_eq 1 (by norm_num)]
    have e2 : sN S0 = 1 := by rw [hS0', LceP.sN_eq, LceP.mkS_eq 1 (by norm_num)]
    rw [e1, e2, hT0']
    exact ⟨le_rfl, rfl, fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := hfold (jAll WT Cs) S0 T0 1 hG0
  rw [← runFacts_eq, ← runLab_eq, ← runIds_eq, Nat.eq_of_beq_eq_true hrun,
    Nat.eq_of_beq_eq_true hlab, Nat.eq_of_beq_eq_true hids, Nat.eq_of_beq_eq_true hS1,
    Nat.eq_of_beq_eq_true hT1] at hG1
  have hL : ∃ rep : ℕ → G, LRefs gen π Ψ blk LB INV nC rep nf := by
    rcases hG1 with h0 | h0 | h0 | h0 | ⟨-, -, rep, -, hrefs⟩
    · rw [LceP.mkS_eq nC hnf'] at h0
      have h0' : nf = 0 := by omega
      exact ⟨fun _ => 1, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (Nat.succ_ne_zero nf)
    · exact absurd h0 one_ne_zero
    · exfalso
      change 4294967296 < nf + 1 at h0
      omega
    · have e1 : sI (mkS nf nC) = nf := by
        rw [LceP.sI_eq, LceP.mkS_eq nC hnf']
        omega
      rw [e1] at hrefs
      exact ⟨rep, hrefs rep fun _ _ => rfl⟩
  obtain ⟨rep, hrefs⟩ := hL
  unfold cycOK at hcyc
  rw [LceP.letB_eq] at hcyc
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.add_eq] at hcyc
  obtain ⟨hk2, hwalk, hlab'⟩ := hcyc
  have hc' : c < 1048576 := by simpa using hc
  have hstart := WL_start gen π Ψ rep (wWord (WT wid)) (wLen (WT wid)) 1 1 hc'
  have hW := walk_cyc gen π Ψ hinv hrefs (wLen (WT wid)) le_rfl R _ _
    (by rw [Nat.sub_self]; exact hstart)
  rw [hwalk, hlab'] at hW
  rcases hW with hdead | ⟨cur, hcur, hst, hX⟩
  · exfalso
    omega
  have hc0 : cur = c := by omega
  have hV0 : aX V ≠ 0 := by
    have := LceP.blt_true hVX
    omega
  rcases hX with h0 | ⟨-, ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩⟩
  · exact absurd h0 hV0
  · refine ⟨a, ?_, congrArg Prod.fst haψ, congrArg (fun x => x.2.1) haψ,
      congrArg (fun x => x.2.2) haψ⟩
    rw [ha, hc0, (hw wid hwid).1 hk2, mul_one, mul_inv_cancel]
  · exact absurd hlt (lt_irrefl _)

theorem catEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {e f b n1 n2 : ℕ}
    (he : entOK e b n1 = true) (hf : entOK f b n2 = true) (hn : n1 + n2 < 1024) :
    entOK (Fi22K.catEnt e f) b (n1 + n2) = true ∧ wLen (Fi22K.catEnt e f) = wLen e + wLen f ∧
      bval gen (wWord (Fi22K.catEnt e f)) (wLen (Fi22K.catEnt e f)) =
        bval gen (wWord e) (wLen e) * bval gen (wWord f) (wLen f) :=
  Co2Kill.catEnt_spec gen he hf hn

theorem letEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {c : ℕ} (hc : c < 254) :
    entOK (Fi22K.letEnt c) 254 1 = true ∧ wLen (Fi22K.letEnt c) = 1 ∧
      bval gen (wWord (Fi22K.letEnt c)) (wLen (Fi22K.letEnt c)) = letV gen c :=
  Co2Kill.letEnt_spec gen hc

theorem e_spec {G : Type*} [Group G] (gen : ℕ → G) {k : ℕ} (hk : eShape k = true) :
    entOK (Fi22K.sigma k) 254 15 = true ∧ entOK (Fi22K.sigInv k) 254 15 = true ∧
      bval gen (wWord (Fi22K.sigInv k)) (wLen (Fi22K.sigInv k)) =
        (bval gen (wWord (Fi22K.sigma k)) (wLen (Fi22K.sigma k)))⁻¹ ∧
      bval gen (wWord (eAB k)) (wLen (eAB k)) =
        (bval gen (wWord (Fi22K.sigma k)) (wLen (Fi22K.sigma k)))⁻¹ * gen 0 *
          bval gen (wWord (Fi22K.sigma k)) (wLen (Fi22K.sigma k)) :=
  Co2Kill.gw_spec gen (GW := eAB) hk

theorem eOK_spec (h : eOK = true) : ∀ k, 1 ≤ k → k ≤ 6 → eShape k = true := by
  have e : eOK = andB (andB (andB (andB (andB (andB true (eShape 1)) (eShape 2))
      (eShape 3)) (eShape 4)) (eShape 5)) (eShape 6) := rfl
  rw [e] at h
  simp only [andB_eq, Bool.and_eq_true, Bool.true_and] at h
  intro k h1 h6
  interval_cases k <;> simp_all

theorem letInvAB_spec {G : Type*} [Group G] (gen : ℕ → G)
    (hE : ∀ k, 1 ≤ k → k ≤ 6 → eShape k = true) {x : ℕ} (hx : x < 12) :
    entOK (Fi22K.letInvAB x) 254 31 = true ∧
      bval gen (wWord (Fi22K.letInvAB x)) (wLen (Fi22K.letInvAB x)) =
        (letV (fun k => bval gen (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))) x)⁻¹ := by
  have hs : Nat.shiftRight x 1 = x / 2 := by
    change x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have hm : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  have e : Fi22K.letInvAB x = Bool.rec (motive := fun _ => ℕ) (eAB (x / 2 + 1))
      (invEnt (eAB (x / 2 + 1))) (Nat.beq (x % 2) 0) := by
    unfold Fi22K.letInvAB
    rw [hs, hm]
  have hg := hE (x / 2 + 1) (by omega) (by omega)
  unfold eShape at hg
  simp only [andB_eq, Bool.and_eq_true] at hg
  have hent : entOK (eAB (x / 2 + 1)) 254 31 = true := Co2Kill.entOK_mono hg.1 (by norm_num) le_rfl
  rw [e]
  have h255 : x ≠ 255 := by omega
  rcases Nat.mod_two_eq_zero_or_one x with h2 | h2
  · rw [h2]
    change entOK (invEnt (eAB (x / 2 + 1))) 254 31 = true ∧
      bval gen (wWord (invEnt (eAB (x / 2 + 1)))) (wLen (invEnt (eAB (x / 2 + 1)))) = _
    obtain ⟨i1, -, i3⟩ := Co2Kill.invEnt_spec gen hent (by norm_num)
    refine ⟨i1, ?_⟩
    rw [i3]
    simp [letV, h255, h2]
  · rw [h2]
    change entOK (eAB (x / 2 + 1)) 254 31 = true ∧
      bval gen (wWord (eAB (x / 2 + 1))) (wLen (eAB (x / 2 + 1))) = _
    refine ⟨hent, ?_⟩
    simp [letV, h255, h2]

theorem piInv_spec {G : Type*} [Group G] (gen : ℕ → G)
    (hE : ∀ k, 1 ≤ k → k ≤ 6 → eShape k = true) {w : ℕ} (hw : entOK w 12 16 = true) :
    entOK (Fi22K.piInv w) 254 496 = true ∧
      bval gen (wWord (Fi22K.piInv w)) (wLen (Fi22K.piInv w)) =
        (bval (fun k => bval gen (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))) (wWord w) (wLen w))⁻¹ := by
  set gen' := fun k => bval gen (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))
  obtain ⟨-, hn, hl⟩ := (entOK_iff _ _ _).1 hw
  set n := wLen w
  set W := wWord w
  set P : ℕ → ℕ := fun k => Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => CFSG.KC.Loop.strictN acc (fun a =>
      Fi22K.catEnt a (Fi22K.letInvAB (CFSG.KC.HOrb.byte W (Nat.sub (Nat.sub n 1) k))))) k
    with hPdef
  have hp : Fi22K.piInv w = P n := rfl
  have key : ∀ k ≤ n, entOK (P k) 254 (31 * k) = true ∧ bval gen (wWord (P k)) (wLen (P k)) =
      ((List.range k).map fun t => (letV gen' (wLet W (n - 1 - t)))⁻¹).prod := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : wLen 0 = 0 := by decide
      refine ⟨Co2Kill.entOK_zero 254, ?_⟩
      change bval gen (wWord 0) (wLen 0) = _
      rw [h0, bval_zero]
      rfl
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : P (k + 1) = Fi22K.catEnt (P k)
          (Fi22K.letInvAB (CFSG.KC.HOrb.byte W (n - 1 - k))) := by
        change CFSG.KC.Loop.strictN (P k) _ = _
        rw [Co2Kill.strictN_eq]
        rfl
      have hx : CFSG.KC.HOrb.byte W (n - 1 - k) < 12 := hl _ (by omega)
      obtain ⟨l1, l2⟩ := letInvAB_spec gen hE hx
      obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 l1 (by omega)
      rw [e, c3, h2, l2, List.range_succ, List.map_append, List.prod_append]
      exact ⟨by rw [Nat.mul_succ]; exact c1, by simp; rfl⟩
  obtain ⟨k1, k2⟩ := key n le_rfl
  refine ⟨by rw [hp]; exact Co2Kill.entOK_mono k1 le_rfl (by omega), ?_⟩
  rw [hp, k2, bval, List.prod_inv_reverse, List.map_map]
  rw [← map_range_rev ((fun x => x⁻¹) ∘ fun i => letV gen' (wLet W i)) n]
  rfl

theorem hWord_spec {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G)
    (hsub : ∀ j, entOK (CFSG.KC.Fi22B.sub j) (nat_lit 4) (nat_lit 17) = true ∧
      bval gen (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j)) ∈ H) (hl : ℕ) :
    ∀ k ≤ 32, entOK (Fi22K.hWord hl k) 254 (17 * k) = true ∧
      bval gen (wWord (Fi22K.hWord hl k)) (wLen (Fi22K.hWord hl k)) ∈ H := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : wLen 0 = 0 := by decide
    refine ⟨Co2Kill.entOK_zero 254, ?_⟩
    change bval gen (wWord 0) (wLen 0) ∈ H
    rw [h0, bval_zero]
    exact H.one_mem
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    set x := CFSG.KC.HOrb.byte hl k
    set q := Bool.rec (motive := fun _ => ℕ) (invEnt (CFSG.KC.Fi22B.sub (Nat.shiftRight x 1)))
      (CFSG.KC.Fi22B.sub (Nat.shiftRight x 1)) (Nat.beq (Nat.land x 1) 0) with hq
    have e : Fi22K.hWord hl (k + 1) = Fi22K.catEnt (Fi22K.hWord hl k) q := by
      have e0 : Fi22K.hWord hl (k + 1) =
          CFSG.KC.Loop.strictN (Fi22K.hWord hl k) (fun a => Fi22K.catEnt a q) := rfl
      rw [e0, Co2Kill.strictN_eq]
    obtain ⟨s1, s2⟩ := hsub (Nat.shiftRight x 1)
    have s1' : entOK (CFSG.KC.Fi22B.sub (Nat.shiftRight x 1)) 254 17 = true :=
      Co2Kill.entOK_mono s1 (by norm_num) le_rfl
    have hq1 : entOK q 254 17 = true ∧ bval gen (wWord q) (wLen q) ∈ H := by
      rw [hq]
      cases Nat.beq (Nat.land x 1) 0
      · obtain ⟨i1, -, i3⟩ := Co2Kill.invEnt_spec gen s1' (by norm_num)
        exact ⟨i1, by rw [i3]; exact H.inv_mem s2⟩
      · exact ⟨s1', s2⟩
    obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 hq1.1 (by omega)
    rw [e, c3]
    exact ⟨by rw [Nat.mul_succ]; exact c1, H.mul_mem h2 hq1.2⟩

theorem pairOK_sound {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) (rep : ℕ → G)
    {blk : ℕ → ℕ} {nf : ℕ} (hrep : rep 0 = 1)
    (hwalk : ∀ w x R y, x < 2 ^ 20 → walkTo blk nf w x R y = true →
      rep x * bval gen (wWord w) (wLen w) * (rep y)⁻¹ ∈ H)
    (hsub : ∀ j, entOK (CFSG.KC.Fi22B.sub j) (nat_lit 4) (nat_lit 17) = true ∧
      bval gen (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j)) ∈ H)
    (hcent : ∀ x ∈ H, x * gen 0 = gen 0 * x) (ha : gen 0 * gen 0 = 1) (hE : eOK = true)
    {UW0 UW1 : ℕ}
    (hU0 : entOK UW0 (nat_lit 4) (nat_lit 64) = true ∧
      ((gen 0)⁻¹ * (bval gen (wWord UW0) (wLen UW0))⁻¹ * gen 0 * bval gen (wWord UW0) (wLen UW0)) ^ 3 = 1)
    (hU1 : entOK UW1 (nat_lit 4) (nat_lit 64) = true ∧
      ((gen 0)⁻¹ * (bval gen (wWord UW1) (wLen UW1))⁻¹ * gen 0 * bval gen (wWord UW1) (wLen UW1)) ^ 2 = 1)
    {XRk i j m w R1 c ρ hl hn R2 : ℕ} (hargs : pairArgsOK i j w hn = true)
    (h : pairOK blk nf UW0 UW1 XRk i j m w R1 c ρ hl hn R2 = true) :
    bval (fun k => bval gen (wWord (eAB (k + 1))) (wLen (eAB (k + 1)))) (wWord XRk) (wLen XRk) = 1 := by
  set gen' : ℕ → G := fun k => bval gen (wWord (eAB (k + 1))) (wLen (eAB (k + 1))) with hgen'
  have hE' := eOK_spec hE
  simp only [pairArgsOK, andB_eq, Bool.and_eq_true, Nat.ble_eq] at hargs
  obtain ⟨hi1, hi6, hj1, hj6, hw, hhn⟩ := hargs
  have hw254 : entOK w 254 16 = true := Co2Kill.entOK_mono hw (by norm_num) le_rfl
  unfold pairOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hX, hw1, hcase⟩ := h
  obtain ⟨si1, si2, si3, si4⟩ := e_spec gen (hE' i hi1 hi6)
  obtain ⟨sj1, -, -, sj4⟩ := e_spec gen (hE' j hj1 hj6)
  set a := gen 0
  set σi := bval gen (wWord (Fi22K.sigma i)) (wLen (Fi22K.sigma i))
  set σj := bval gen (wWord (Fi22K.sigma j)) (wLen (Fi22K.sigma j))
  set πw := bval gen' (wWord w) (wLen w)
  obtain ⟨p1, p2⟩ := piInv_spec gen hE' hw
  obtain ⟨c1, -, c3⟩ := catEnt_spec gen p1 si2 (by norm_num)
  obtain ⟨-, -, d3⟩ := catEnt_spec gen sj1 c1 (by norm_num)
  have hPv : bval gen (wWord (Fi22K.pairWord i j w)) (wLen (Fi22K.pairWord i j w)) =
      σj * (πw⁻¹ * σi⁻¹) := by
    unfold Fi22K.pairWord
    rw [d3, c3, p2, si3]
  have hwk1 := hwalk _ 0 R1 c (by norm_num) hw1
  rw [bval_withSent, hPv, hrep, one_mul] at hwk1
  have hlet : ∀ t, 1 ≤ t → t ≤ 6 →
      letV gen' (2 * (t - 1)) = bval gen (wWord (eAB t)) (wLen (eAB t)) := by
    intro t h1 h6
    have e1 : 2 * (t - 1) ≠ 255 := by omega
    have e2 : 2 * (t - 1) % 2 = 0 := by omega
    have e3 : 2 * (t - 1) / 2 + 1 = t := by omega
    simp only [letV, e1, e2, ite_false, ite_true]
    change bval gen (wWord (eAB (2 * (t - 1) / 2 + 1))) (wLen (eAB (2 * (t - 1) / 2 + 1))) = _
    rw [e3]
  obtain ⟨ej1, -, ej3⟩ := letEnt_spec gen' (c := 2 * (j - 1)) (by omega)
  obtain ⟨ewj1, -, ewj3⟩ := catEnt_spec gen' hw254 ej1 (by norm_num)
  obtain ⟨ei1, -, ei3⟩ := letEnt_spec gen' (c := 2 * (i - 1)) (by omega)
  obtain ⟨eiwj1, -, eiwj3⟩ := catEnt_spec gen' ei1 ewj1 (by norm_num)
  obtain ⟨ev1, -, ev3⟩ := Co2Kill.invEnt_spec gen' hw254 (by norm_num)
  obtain ⟨ea1, -, ea3⟩ := catEnt_spec gen' ev1 eiwj1 (by norm_num)
  obtain ⟨eW, eL, -⟩ := (entOK_iff _ _ _).1 ea1
  have hcase' : (∃ U mU : ℕ, m = mU ∧ mU ≤ 3 ∧
      walkTo blk nf (withSent (Fi22K.catEnt U (Fi22K.hWord hl hn))) 0 R2 c = true ∧
      entOK U (nat_lit 4) (nat_lit 64) = true ∧
      ((gen 0)⁻¹ * (bval gen (wWord U) (wLen U))⁻¹ * gen 0 * bval gen (wWord U) (wLen U)) ^ mU = 1) ∨
      (c = 0 ∧ m = 1) := by
    cases hρ : Nat.beq ρ 0 <;> rw [hρ] at hcase <;> dsimp only at hcase
    · cases hρ1 : Nat.beq ρ 1 <;> rw [hρ1] at hcase <;> dsimp only at hcase <;>
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcase
      · exact Or.inl ⟨UW1, 2, hcase.1, by norm_num, hcase.2.2, hU1⟩
      · exact Or.inl ⟨UW0, 3, hcase.1, le_rfl, hcase.2.2, hU0⟩
    · simp only [Bool.and_eq_true, Nat.beq_eq] at hcase
      exact Or.inr hcase
  have hm3 : m ≤ 3 := by
    rcases hcase' with ⟨U, mU, hm, hmU, -⟩ | ⟨-, hm⟩
    · omega
    · omega
  have hXv : bval gen' (wWord XRk) (wLen XRk) =
      (πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj)))) ^ m := by
    have hX' : Fi22K.xrelOf i j m w = powEnt (Fi22K.catEnt (invEnt w) (Fi22K.catEnt
        (Fi22K.letEnt (2 * (i - 1))) (Fi22K.catEnt w (Fi22K.letEnt (2 * (j - 1)))))) m := rfl
    rw [← hX, hX', bval_powEnt gen' eW
      (lt_of_le_of_lt (Nat.mul_le_mul hm3 eL) (by norm_num)), ea3, ev3, eiwj3, ei3, ewj3, ej3,
      hlet i hi1 hi6, hlet j hj1 hj6, si4, sj4]
  rw [hXv]
  have hre : πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj))) =
      (σi * πw)⁻¹ * a * (σi * πw) * σj⁻¹ * a * σj := by group
  have hvu : σj * (πw⁻¹ * σi⁻¹) = σj * (σi * πw)⁻¹ := by group
  rw [hre]
  rw [hvu] at hwk1
  rcases hcase' with ⟨U, mU, hm, -, hw2, u1, u2⟩ | ⟨hc0, hm1⟩
  ·
    obtain ⟨hh1, hh2⟩ := hWord_spec gen H hsub hl hn hhn
    obtain ⟨-, -, f3⟩ := catEnt_spec gen (Co2Kill.entOK_mono u1 (by norm_num) le_rfl)
      (Co2Kill.entOK_mono hh1 le_rfl (n' := 544) (by omega)) (by norm_num)
    have hwk2 := hwalk _ 0 R2 c (by norm_num) hw2
    rw [bval_withSent, f3, hrep, one_mul] at hwk2
    rw [hm]
    refine Co2Kill.pair_group H ha hcent (H.mul_mem hwk1 (H.inv_mem hwk2)) hh2 ?_ u2
    group
  ·
    rw [hc0, hrep, inv_one, mul_one] at hwk1
    rw [hm1]
    refine Co2Kill.pair_group H ha hcent (U := 1) hwk1 H.one_mem ?_ (by group)
    group

end CFSG.Certificates.Fi22Kill

end
