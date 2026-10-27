module

public import Certificates.Data.Kernel.GL62.Lanes
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Code
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.GL62.LS

open CFSG.KC.GL62 CFSG.KC.Misc.Spec CFSG.OddStandard.AltStdSmall4.GL62

@[expose] def ofF : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | N + 1, f => f 0 + 2 ^ 64 * ofF N fun t => f (t + 1)

theorem ofF_zero_fun (N : ℕ) : (ofF N fun _ => 0) = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [ofF, ih, Nat.mul_zero]

theorem ofF_succ (N : ℕ) (f : ℕ → ℕ) : ofF (N + 1) f = f 0 + 2 ^ 64 * ofF N fun t => f (t + 1) :=
  rfl

theorem testBit_lane {a : ℕ} (A : ℕ) (ha : a < 2 ^ 64) (i : ℕ) :
    (a + 2 ^ 64 * A).testBit i = if i < 64 then a.testBit i else A.testBit (i - 64) := by
  rw [Nat.add_comm]
  exact Nat.testBit_two_pow_mul_add A ha i

theorem ofF_land {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (hg : ∀ t < N, g t < 2 ^ 64) :
    ofF N f &&& ofF N g = ofF N fun t => f t &&& g t := by
  induction N generalizing f g with
  | zero => simp [ofF]
  | succ N ih =>
    rw [ofF_succ, ofF_succ, ofF_succ,
      ← ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega))]
    have h0 := hf 0 (by omega)
    have h1 := hg 0 (by omega)
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, testBit_lane _ h0, testBit_lane _ h1,
      testBit_lane _ (Nat.and_lt_two_pow _ h1)]
    split <;> simp [Nat.testBit_and]

theorem ofF_xor {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (hg : ∀ t < N, g t < 2 ^ 64) :
    ofF N f ^^^ ofF N g = ofF N fun t => f t ^^^ g t := by
  induction N generalizing f g with
  | zero => simp [ofF]
  | succ N ih =>
    rw [ofF_succ, ofF_succ, ofF_succ,
      ← ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega))]
    have h0 := hf 0 (by omega)
    have h1 := hg 0 (by omega)
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, testBit_lane _ h0, testBit_lane _ h1,
      testBit_lane _ (Nat.xor_lt_two_pow h0 h1)]
    split <;> simp [Nat.testBit_xor]

theorem ofF_mul (N : ℕ) (f : ℕ → ℕ) (c : ℕ) : ofF N f * c = ofF N fun t => f t * c := by
  induction N generalizing f with
  | zero => simp [ofF]
  | succ N ih =>
    rw [ofF_succ, ofF_succ, ← ih]
    ring

theorem ofF_shift_mask {N s m : ℕ} {f : ℕ → ℕ} (hs : s ≤ 64) (hm : m < 2 ^ (64 - s))
    (hf : ∀ t < N, f t < 2 ^ 64) :
    (ofF N f >>> s) &&& (ofF N fun _ => m) = ofF N fun t => (f t >>> s) &&& m := by
  induction N generalizing f with
  | zero => simp [ofF]
  | succ N ih =>
    have hm64 : m < 2 ^ 64 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h0 := hf 0 (by omega)
    rw [ofF_succ, ofF_succ, ofF_succ (f := fun t => (f t >>> s) &&& m),
      ← ih (fun t ht => hf (t + 1) (by omega))]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lane _ h0, testBit_lane _ hm64,
      testBit_lane _ (Nat.and_lt_two_pow _ hm64), Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hi : i < 64
    · simp only [hi, if_true]
      by_cases his : s + i < 64
      · simp [his]
      · have : m.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [this]
    · simp only [hi, if_false, show ¬ s + i < 64 by omega]
      rw [show s + i - 64 = s + (i - 64) by omega, Nat.testBit_and, Nat.testBit_shiftRight]

theorem repu_succ' (s N : ℕ) : repu s (N + 1) = 1 + 2 ^ s * repu s N := by
  unfold repu
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm, Nat.mul_zero, pow_zero]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [Nat.mul_succ, pow_add, mul_comm]

theorem ofF_one_eq_repu (N : ℕ) : (ofF N fun _ => 1) = repu 64 N := by
  induction N with
  | zero => simp [ofF, repu]
  | succ N ih => rw [ofF_succ, ih, repu_succ' 64 N]

theorem lrep_eq (N : ℕ) : lrep N = ofF N fun _ => 1 := by
  rw [ofF_one_eq_repu, repu_eq (by norm_num)]
  unfold lrep W64
  rw [shl1_eq]
  rfl

theorem const_mul_lrep (c N : ℕ) : c * lrep N = ofF N fun _ => c := by
  rw [lrep_eq, Nat.mul_comm, ofF_mul]
  simp

theorem packL_eq_ofF {xs : List ℕ} (hx : ∀ x ∈ xs, x < 2 ^ 64) :
    packL xs = ofF xs.length fun t => xs.getD t 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h0 := hx x List.mem_cons_self
    rw [List.length_cons, ofF_succ]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [← ih fun y hy => hx y (List.mem_cons_of_mem _ hy)]
    change (x ||| (packL xs <<< 64)) = _
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.shiftLeft_eq, testBit_lane _ h0,
      Nat.testBit_mul_two_pow]
    by_cases hi : i < 64
    · simp [hi, show ¬ 64 ≤ i by omega]
    · have hx : x.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h0 (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi, hx, show 64 ≤ i by omega]

theorem laneK_eq (P k : ℕ) : laneK P k = P / 2 ^ (64 * k) % 2 ^ 64 := by
  unfold laneK W64
  change (P >>> (64 * k)) &&& (2 ^ 64 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem laneK_ofF {N : ℕ} {f : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (k : ℕ) :
    laneK (ofF N f) k = if k < N then f k else 0 := by
  rw [laneK_eq]
  induction N generalizing f k with
  | zero => simp [ofF]
  | succ N ih =>
    rw [ofF_succ]
    have h0 := hf 0 (by omega)
    cases k with
    | zero =>
      rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0,
        if_pos (Nat.succ_pos N)]
    | succ k =>
      have e : 64 * (k + 1) = 64 + 64 * k := by ring
      rw [e, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt h0, Nat.zero_add, ih (fun t ht => hf (t + 1) (by omega))]
      simp

theorem laneK_packL {xs : List ℕ} (hx : ∀ x ∈ xs, x < 2 ^ 64) (k : ℕ) :
    laneK (packL xs) k = xs.getD k 0 := by
  rw [packL_eq_ofF hx, laneK_ofF (fun t ht => hx _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht)) k]
  split_ifs with hk
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

theorem ofF_inj {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (hg : ∀ t < N, g t < 2 ^ 64)
    (h : ofF N f = ofF N g) : ∀ t < N, f t = g t := by
  intro t ht
  have := congrArg (laneK · t) h
  simpa [laneK_ofF hf, laneK_ofF hg, ht] using this

theorem ofF_congr {N : ℕ} {f g : ℕ → ℕ} (h : ∀ t < N, f t = g t) : ofF N f = ofF N g := by
  induction N generalizing f g with
  | zero => rfl
  | succ N ih =>
    rw [ofF_succ, ofF_succ, h 0 (by omega), ih fun t ht => h (t + 1) (by omega)]

theorem ofF_add (N : ℕ) (f g : ℕ → ℕ) : ofF N f + ofF N g = ofF N fun t => f t + g t := by
  induction N generalizing f g with
  | zero => rfl
  | succ N ih =>
    rw [ofF_succ, ofF_succ, ofF_succ, ← ih]
    ring

theorem ofF_snoc (N : ℕ) (f : ℕ → ℕ) : ofF (N + 1) f = ofF N f + 2 ^ (64 * N) * f N := by
  induction N generalizing f with
  | zero => simp [ofF]
  | succ N ih =>
    have e : 64 * (N + 1) = 64 + 64 * N := by ring
    rw [ofF_succ, ih, ofF_succ (N := N), e, Nat.pow_add]
    ring

theorem ofF_sub {N : ℕ} {f g : ℕ → ℕ} (h : ∀ t < N, g t ≤ f t) :
    ofF N f - ofF N g = ofF N fun t => f t - g t := by
  have : ofF N f = (ofF N fun t => f t - g t) + ofF N g := by
    rw [ofF_add]
    exact ofF_congr fun t ht => by have := h t ht; omega
  omega

theorem ofF_lor {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 64) (hg : ∀ t < N, g t < 2 ^ 64) :
    ofF N f ||| ofF N g = ofF N fun t => f t ||| g t := by
  induction N generalizing f g with
  | zero => simp [ofF]
  | succ N ih =>
    rw [ofF_succ, ofF_succ, ofF_succ,
      ← ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega))]
    have h0 := hf 0 (by omega)
    have h1 := hg 0 (by omega)
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, testBit_lane _ h0, testBit_lane _ h1,
      testBit_lane _ (Nat.or_lt_two_pow h0 h1)]
    split <;> simp [Nat.testBit_or]

theorem ofF_mul_one (N : ℕ) (b : ℕ → ℕ) : ∃ R, ofF N b * (ofF N fun _ => 1) =
    (ofF N fun k => ∑ i ∈ Finset.range (k + 1), b i) + 2 ^ (64 * N) * R := by
  induction N generalizing b with
  | zero => exact ⟨0, by simp [ofF]⟩
  | succ N ih =>
    obtain ⟨R, hR⟩ := ih fun t => b (t + 1)
    refine ⟨R + ofF N fun t => b (t + 1), ?_⟩
    have e1 : (ofF (N + 1) fun _ => 1) = (ofF N fun _ => 1) + 2 ^ (64 * N) := by
      rw [ofF_snoc]
      ring
    have e0 : b 0 * (ofF (N + 1) fun _ => 1) = ofF (N + 1) fun _ => b 0 := by
      rw [Nat.mul_comm, ofF_mul]
      simp
    have e2 : ofF (N + 1) b * (ofF (N + 1) fun _ => 1) =
        (ofF (N + 1) fun _ => b 0) + 2 ^ 64 * ((ofF N fun t => b (t + 1)) * (ofF N fun _ => 1)) +
          2 ^ 64 * 2 ^ (64 * N) * (ofF N fun t => b (t + 1)) := by
      calc ofF (N + 1) b * (ofF (N + 1) fun _ => 1)
          = b 0 * (ofF (N + 1) fun _ => 1) +
            2 ^ 64 * ((ofF N fun t => b (t + 1)) * (ofF (N + 1) fun _ => 1)) := by
            rw [ofF_succ N b]
            ring
        _ = _ := by
            rw [e0, e1]
            ring
    have e4 : (ofF (N + 1) fun k => ∑ i ∈ Finset.range (k + 1), b i) =
        b 0 + 2 ^ 64 * ofF N fun t => ∑ i ∈ Finset.range (t + 1 + 1), b i := by
      simp only [ofF_succ, Finset.sum_range_one, Nat.zero_add]
    have e5 : (ofF (N + 1) fun _ => b 0) = b 0 + 2 ^ 64 * ofF N fun _ => b 0 := ofF_succ N _
    have e3 : (ofF N fun t => ∑ i ∈ Finset.range (t + 1 + 1), b i) =
        (ofF N fun _ => b 0) + ofF N fun k => ∑ i ∈ Finset.range (k + 1), b (i + 1) := by
      rw [ofF_add]
      refine ofF_congr fun t _ => ?_
      rw [Finset.sum_range_succ' _ (t + 1)]
      ring
    have e6 : (2 : ℕ) ^ (64 * (N + 1)) = 2 ^ 64 * 2 ^ (64 * N) := by
      rw [← Nat.pow_add]
      ring_nf
    rw [e2, hR, e4, e5, e3, e6]
    ring

theorem laneK_add_high (X R k : ℕ) : laneK (X + 2 ^ (64 * (k + 1)) * R) k = laneK X k := by
  have e : 64 * (k + 1) = 64 * k + 64 := by ring
  rw [laneK_eq, laneK_eq, e, Nat.pow_add, mul_assoc, Nat.add_mul_div_left _ _ (by positivity),
    Nat.add_mul_mod_self_left]

theorem nzL_ofF {N : ℕ} (hN : 0 < N) (hN' : N ≤ 4294967296) {z : ℕ → ℕ}
    (hz : ∀ t < N, z t < 2 ^ 36) :
    nzL N (lrep N) (ofF N z) = ∑ i ∈ Finset.range N, if z i = 0 then 0 else 1 := by
  have hz64 : ∀ t < N, z t + 68719476735 < 2 ^ 64 := fun t ht => by
    have := hz t ht
    norm_num at this ⊢
    omega
  have e1 : ofF N z + 68719476735 * lrep N = ofF N fun t => z t + 68719476735 := by
    rw [const_mul_lrep, ofF_add]
  have e2 : (ofF N fun t => z t + 68719476735) >>> 36 &&& lrep N =
      ofF N fun t => if z t = 0 then 0 else 1 := by
    rw [lrep_eq, ofF_shift_mask (by norm_num) (by norm_num) hz64]
    refine ofF_congr fun t ht => ?_
    have := hz t ht
    rw [Nat.shiftRight_eq_div_pow]
    split_ifs with h0
    · rw [h0, Nat.div_eq_of_lt (by norm_num)]
      rfl
    · have e : (z t + 68719476735) / 2 ^ 36 = 1 := by
        apply Nat.div_eq_of_lt_le
        · norm_num
          omega
        · norm_num at this ⊢
          omega
      rw [e]
      rfl
  obtain ⟨R, hR⟩ := ofF_mul_one N fun t => if z t = 0 then 0 else 1
  unfold nzL
  change laneK (((ofF N z + 68719476735 * lrep N) >>> 36 &&& lrep N) * lrep N) (N - 1) = _
  rw [e1, e2, lrep_eq, hR]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel, laneK_add_high, laneK_ofF]
  · simp
  · intro t ht
    refine lt_of_le_of_lt (Finset.sum_le_card_nsmul _ _ 1 fun i _ => by split_ifs <;> omega) ?_
    simp only [Finset.card_range, smul_eq_mul, Nat.mul_one]
    norm_num
    omega

theorem geL_ofF {N m : ℕ} (hm : m < 2 ^ 36) {y : ℕ → ℕ} (hy : ∀ t < N, y t < 2 ^ 36)
    (h : geL (lrep N) (ofF N y) m = true) : ∀ t < N, m ≤ y t := by
  unfold geL at h
  have hG : lrep N <<< 36 = ofF N fun _ => 2 ^ 36 := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm, const_mul_lrep]
  have hl : ∀ (v : ℕ) (k : ℕ → Bool), CFSG.KC.LQT.P.letB v k = k v := fun v k => by
    cases v <;> rfl
  rw [hl] at h
  change Nat.beq (((ofF N y ||| lrep N <<< 36) - m * lrep N) &&& lrep N <<< 36)
    (lrep N <<< 36) = true at h
  have h64 : ∀ t < N, y t < 2 ^ 64 := fun t ht => lt_of_lt_of_le (hy t ht) (Nat.pow_le_pow_right
    (by norm_num) (by norm_num))
  have hor : ∀ t < N, (y t ||| 2 ^ 36) = y t + 2 ^ 36 := fun t ht => by
    have := Nat.two_pow_add_eq_or_of_lt (hy t ht) 1
    rw [Nat.mul_one] at this
    rw [Nat.or_comm, ← this, Nat.add_comm]
  have hsub : ∀ t < N, (fun _ => m) t ≤ (fun t => y t + 2 ^ 36) t := fun t _ => by
    simp only
    omega
  have hland : ∀ t < N, (fun t => y t + 2 ^ 36 - m) t < 2 ^ 64 := fun t ht => by
    have := hy t ht
    simp only
    norm_num at this ⊢
    omega
  have hc : ∀ t < N, (fun _ => (2 : ℕ) ^ 36) t < 2 ^ 64 := fun _ _ => by norm_num
  rw [hG, ofF_lor h64 hc, const_mul_lrep, ofF_congr hor, ofF_sub hsub, ofF_land hland hc,
    Nat.beq_eq] at h
  intro t ht
  have hf2 : ∀ t < N, (fun t => (y t + 2 ^ 36 - m) &&& 2 ^ 36) t < 2 ^ 64 := fun t _ =>
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have key := ofF_inj hf2 hc h t ht
  have hle : (y t + 2 ^ 36 - m) &&& 2 ^ 36 ≤ y t + 2 ^ 36 - m := Nat.and_le_left
  rw [key] at hle
  omega

theorem mulL_scalar (A B : ℕ) : mulL R6 63 A B = CFSG.KC.Misc.G24.mulF2 6 A B := by
  unfold mulL CFSG.KC.Misc.G24.mulF2
  simp only [CFSG.KS.PK.letN_eq]
  rfl

theorem mat_eq_pk (x : ℕ) : Code.mat x = (pkMat 6 x).transpose := by
  ext i j
  rfl

@[expose] noncomputable def foldL (Rl Fl A B n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc ^^^
    ((A >>> k &&& Rl) * 63 &&& (B >>> (6 * k) &&& Fl) * R6)) n

theorem mulL_eq_foldL (Rl Fl A B : ℕ) : mulL Rl Fl A B = foldL Rl Fl A B 6 := by
  unfold mulL foldL
  simp only [CFSG.KS.PK.letN_eq]
  rfl

theorem foldL_lt (A B n : ℕ) : foldL R6 63 A B n < 2 ^ 36 := by
  induction n with
  | zero => norm_num [foldL]
  | succ n ih =>
    refine Nat.xor_lt_two_pow ih (lt_of_le_of_lt (Nat.and_le_left) ?_)
    calc (A >>> n &&& R6) * 63 ≤ R6 * 63 := Nat.mul_le_mul_right _ Nat.and_le_right
      _ < 2 ^ 36 := by unfold R6; norm_num

theorem mulL_scalar_lt (A B : ℕ) : mulL R6 63 A B < 2 ^ 36 := by
  rw [mulL_eq_foldL]
  exact foldL_lt A B 6

theorem two36_le : (2 : ℕ) ^ 36 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem mulL_ofF {N : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < N, f t < 2 ^ 36) (hg : ∀ t < N, g t < 2 ^ 36) :
    mulL (ofF N fun _ => R6) (ofF N fun _ => 63) (ofF N f) (ofF N g) =
      ofF N fun t => mulL R6 63 (f t) (g t) := by
  have hf64 : ∀ t < N, f t < 2 ^ 64 := fun t ht => lt_of_lt_of_le (hf t ht) two36_le
  have hg64 : ∀ t < N, g t < 2 ^ 64 := fun t ht => lt_of_lt_of_le (hg t ht) two36_le
  have hR : R6 < 2 ^ 31 := by unfold R6; norm_num
  have key : ∀ n ≤ 6, foldL (ofF N fun _ => R6) (ofF N fun _ => 63) (ofF N f) (ofF N g) n =
      ofF N fun t => foldL R6 63 (f t) (g t) n := by
    intro n hn
    induction n with
    | zero => simp [foldL, ofF_zero_fun]
    | succ n ih =>
      have e1 := ofF_shift_mask (s := n) (m := R6) (by omega)
        (lt_of_lt_of_le hR (Nat.pow_le_pow_right (by norm_num) (by omega))) hf64
      have e2 := ofF_shift_mask (s := 6 * n) (m := 63) (by omega)
        (lt_of_lt_of_le (by norm_num : (63 : ℕ) < 2 ^ 6) (Nat.pow_le_pow_right (by norm_num)
          (by omega))) hg64
      change foldL _ _ _ _ n ^^^ _ = ofF N fun t => foldL R6 63 (f t) (g t) n ^^^ _
      rw [ih (by omega), e1, e2, ofF_mul, ofF_mul, ofF_land, ofF_xor]
      · exact fun t _ => lt_of_lt_of_le (foldL_lt _ _ n) two36_le
      · intro t _
        refine lt_of_le_of_lt Nat.and_le_left ?_
        calc (f t >>> n &&& R6) * 63 ≤ R6 * 63 := Nat.mul_le_mul_right _ Nat.and_le_right
          _ < 2 ^ 64 := by unfold R6; norm_num
      · intro t _
        calc (f t >>> n &&& R6) * 63 ≤ R6 * 63 := Nat.mul_le_mul_right _ Nat.and_le_right
          _ < 2 ^ 64 := by unfold R6; norm_num
      · intro t _
        calc (g t >>> (6 * n) &&& 63) * R6 ≤ 63 * R6 := Nat.mul_le_mul_right _ Nat.and_le_right
          _ < 2 ^ 64 := by unfold R6; norm_num
  rw [mulL_eq_foldL, key 6 le_rfl]
  simp only [mulL_eq_foldL]

theorem cmulK_eq (a b : ℕ) : cmulK a b = Code.mul a b := by
  refine Code.eq_of_mat_eq (mulL_scalar_lt _ _) (Code.mul_lt _ _) ?_
  rw [Code.mat_mul, mat_eq_pk, mat_eq_pk, mat_eq_pk, cmulK, mulL_scalar, pkMat_mulF2,
    Matrix.transpose_mul]

end CFSG.KC.GL62.LS

end
