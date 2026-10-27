module

public import CFSG.Certificates.Kernel.TcRes.MovedSound
public import Certificates.Data.Kernel.TcRes.C3

public section

namespace CFSG.KC.TcRes

open CFSG.TcRes.TK CFSG.KC.TcRes.Lane

@[expose] def sv (x : ℕ) : ℤ := (x : ℤ) - 4294967296

theorem sv_ofs : sv OFS = 0 := by
  change ((4294967296 : ℕ) : ℤ) - 4294967296 = 0
  norm_num

theorem sv_inj {x y : ℕ} (h : sv x = sv y) : x = y := by
  unfold sv at h
  omega

theorem sv_spk (a b : ℕ) (hb : b ≤ 4294967296) : sv (spk a b) = (a : ℤ) - b := by
  have e : spk a b = 4294967296 + a - b := rfl
  rw [sv, e]
  omega

theorem sv_sadd {x y : ℕ} (h : -4294967296 ≤ sv x + sv y) : sv (sadd x y) = sv x + sv y := by
  have e : sadd x y = x + y - 4294967296 := rfl
  unfold sv at h ⊢
  rw [e]
  omega

theorem sv_smul {x y : ℕ} (h : -4294967296 ≤ sv x * sv y) : sv (smul x y) = sv x * sv y := by
  have e : smul x y = x * y + (18446744073709551616 + 4294967296) - 4294967296 * (x + y) := rfl
  have key : ((x * y + (18446744073709551616 + 4294967296) : ℕ) : ℤ) -
      ((4294967296 * (x + y) : ℕ) : ℤ) = sv x * sv y + 4294967296 := by
    push_cast
    unfold sv
    ring
  have hle : ((4294967296 * (x + y) : ℕ) : ℤ) ≤ ((x * y + (18446744073709551616 + 4294967296) : ℕ) : ℤ) := by
    linarith
  have hle' : 4294967296 * (x + y) ≤ x * y + (18446744073709551616 + 4294967296) := by
    exact_mod_cast hle
  rw [e]
  unfold sv at key ⊢
  rw [Nat.cast_sub hle']
  linarith

theorem ssum_succ (c : ℕ) (f : ℕ → ℕ) : ssum (c + 1) f = sadd (f c) (ssum c f) := by
  have e : ssum (c + 1) f = strictN (ssum c f) (fun a => sadd (f c) a) := rfl
  rw [strictN_eq] at e
  exact e

theorem sv_ssum (f : ℕ → ℕ) (B : ℤ) : ∀ c, (∀ j < c, |sv (f j)| ≤ B) → c * B < 4294967296 →
    sv (ssum c f) = ∑ j ∈ Finset.range c, sv (f j) ∧ |∑ j ∈ Finset.range c, sv (f j)| ≤ c * B := by
  intro c
  induction c with
  | zero =>
    intro _ _
    refine ⟨sv_ofs, ?_⟩
    simp
  | succ c ih =>
    intro hf hB
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hf 0 (by omega))
    obtain ⟨i1, i2⟩ := ih (fun j hj => hf j (by omega)) (by push_cast at hB ⊢; linarith)
    have hc := abs_le.1 (hf c (by omega))
    have hs := abs_le.1 i2
    rw [ssum_succ, Finset.sum_range_succ, sv_sadd (by rw [i1]; push_cast at hB; linarith), i1]
    refine ⟨by ring, abs_le.2 ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith

theorem smoothN_iff (n : ℕ) : smoothN n = true ↔ n ≠ 0 ∧ n ∣ 30 ^ 64 := by
  have e : smoothN n = CFSG.TcRes.TK.andB (Nat.blt 0 n) (Nat.beq (30 ^ 64 % n) 0) := rfl
  rw [e, andB_eq_true, blt_eq_true, beq_eq_true, Nat.dvd_iff_mod_eq_zero]
  omega

theorem cols_spec {PW COLS : ℕ} (h : colsOK PW COLS = true) :
    (∀ k < 8, fld COLS 8 k < 240) ∧ ∀ i < 4, fld COLS 8 (2 * i + 1) = fld PW 8 (fld COLS 8 (2 * i)) := by
  have e : colsOK PW COLS = CFSG.TcRes.TK.andB (allLt 8 fun k => Nat.blt (fld COLS 8 k) 240)
      (allLt 4 fun i => Nat.beq (fld COLS 8 (2 * i + 1)) (fld PW 8 (fld COLS 8 (2 * i)))) := rfl
  rw [e, andB_eq_true] at h
  exact ⟨fun k hk => blt_eq_true.1 (Lane.allLt_iff.1 h.1 k hk),
    fun i hi => beq_eq_true.1 (Lane.allLt_iff.1 h.2 i hi)⟩

theorem sabs_eq (x : ℕ) : (sabs x : ℤ) = |sv x| := by
  have e : sabs x = Bool.rec (motive := fun _ => ℕ) (4294967296 - x) (x - 4294967296)
      (Nat.ble 4294967296 x) := rfl
  rw [e, boolRec_nat]
  unfold sv
  split_ifs with h
  · have := ble_eq_true.1 h
    rw [abs_of_nonneg (by omega)]
    omega
  · have : ¬ 4294967296 ≤ x := fun h' => h (ble_eq_true.2 h')
    rw [abs_of_neg (by omega)]
    omega

theorem prod_bound {u v : ℕ} (hu : u < 16) (hv : v < 2 ^ 8) :
    -2048 ≤ ((u : ℤ) - 7) * ((v : ℤ) - 128) ∧ ((u : ℤ) - 7) * ((v : ℤ) - 128) ≤ 2048 := by
  have hv' : v < 256 := lt_of_lt_of_eq hv (by norm_num)
  have ha : |(u : ℤ) - 7| ≤ 8 := abs_le.2 ⟨by omega, by omega⟩
  have hb : |(v : ℤ) - 128| ≤ 128 := abs_le.2 ⟨by omega, by omega⟩
  have h := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
  rw [← abs_mul] at h
  have := abs_le.1 h
  constructor <;> linarith [this.1, this.2]

theorem bx_spec {V COLS XM DD : ℕ} (hVl : ∀ k < 8, ∀ m < 8, fld (fld V 128 (fld COLS 8 k)) 16 m < 16)
    (h : bxOK V COLS XM DD = true) :
    (DD : ℤ) - 128 ≠ 0 ∧ ((DD : ℤ) - 128).natAbs ∣ 30 ^ 64 ∧ ∀ i < 8, ∀ j < 8,
      ∑ k ∈ Finset.range 8, ((fld (fld V 128 (fld COLS 8 k)) 16 i : ℤ) - 7) *
        ((fld XM 8 (8 * k + j) : ℤ) - 128) = if i = j then (DD : ℤ) - 128 else 0 := by
  have e : bxOK V COLS XM DD = CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (Nat.beq (spk DD 128) OFS))
      (CFSG.TcRes.TK.andB (smoothN (sabs (spk DD 128))) (allLt 8 fun i => allLt 8 fun j =>
        Nat.beq (ssum 8 fun k => smul (rco V (fld COLS 8 k) i) (xe XM k j))
          (Bool.rec (motive := fun _ => ℕ) OFS (spk DD 128) (Nat.beq i j)))) := by
    unfold bxOK
    rw [strictB_eq]
  rw [e, andB_eq_true, andB_eq_true, notB_eq_true, beq_eq_false, smoothN_iff] at h
  obtain ⟨h0, ⟨hs0, hsd⟩, hm⟩ := h
  have hd : sv (spk DD 128) = (DD : ℤ) - 128 := sv_spk DD 128 (by norm_num)
  have habs : sabs (spk DD 128) = ((DD : ℤ) - 128).natAbs := by
    have := sabs_eq (spk DD 128)
    rw [hd, ← Int.natCast_natAbs] at this
    exact_mod_cast this
  refine ⟨fun h' => h0 (sv_inj (by rw [hd, h', sv_ofs])), habs ▸ hsd, fun i hi j hj => ?_⟩
  have hij := beq_eq_true.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 hm i hi) j hj)
  have hr : ∀ k < 8, sv (rco V (fld COLS 8 k) i) = (fld (fld V 128 (fld COLS 8 k)) 16 i : ℤ) - 7 :=
    fun k _ => sv_spk _ 7 (by norm_num)
  have hx : ∀ k, sv (xe XM k j) = (fld XM 8 (8 * k + j) : ℤ) - 128 :=
    fun k => sv_spk _ 128 (by norm_num)
  have hp : ∀ k < 8, -4294967296 ≤ sv (rco V (fld COLS 8 k) i) * sv (xe XM k j) := by
    intro k hk
    rw [hr k hk, hx k]
    linarith [(prod_bound (hVl k hk i hi) (fld_lt XM 8 (8 * k + j))).1]
  have hb : ∀ k < 8, |sv (smul (rco V (fld COLS 8 k) i) (xe XM k j))| ≤ 2048 := by
    intro k hk
    rw [sv_smul (hp k hk), hr k hk, hx k, abs_le]
    exact prod_bound (hVl k hk i hi) (fld_lt XM 8 (8 * k + j))
  obtain ⟨hsum, _⟩ := sv_ssum _ 2048 8 hb (by norm_num)
  have hsv := congrArg sv hij
  rw [hsum] at hsv
  have hterm : ∀ k ∈ Finset.range 8, sv (smul (rco V (fld COLS 8 k) i) (xe XM k j)) =
      ((fld (fld V 128 (fld COLS 8 k)) 16 i : ℤ) - 7) * ((fld XM 8 (8 * k + j) : ℤ) - 128) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [sv_smul (hp k hk'), hr k hk', hx k]
  rw [Finset.sum_congr rfl hterm] at hsv
  rw [hsv, boolRec_nat]
  by_cases hq : i = j
  · rw [if_pos (beq_eq_true.2 hq), if_pos hq, hd]
  · rw [if_neg (fun h' => hq (beq_eq_true.1 h')), if_neg hq, sv_ofs]

theorem sv_smul_bd {x y : ℕ} {A B : ℤ} (hx : |sv x| ≤ A) (hy : |sv y| ≤ B)
    (hAB : A * B < 4294967296) : sv (smul x y) = sv x * sv y ∧ |sv x * sv y| ≤ A * B := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hx
  have hm : |sv x * sv y| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hA
  refine ⟨sv_smul ?_, hm⟩
  linarith [(abs_le.1 hm).1]

theorem sv_sadd_bd {x y : ℕ} {A B : ℤ} (hx : |sv x| ≤ A) (hy : |sv y| ≤ B)
    (hAB : A + B < 4294967296) : sv (sadd x y) = sv x + sv y ∧ |sv x + sv y| ≤ A + B := by
  have h1 := abs_le.1 hx
  have h2 := abs_le.1 hy
  refine ⟨sv_sadd (by linarith), abs_le.2 ⟨by linarith, by linarith⟩⟩

theorem sv_sneg_bd {x : ℕ} {A : ℤ} (hx : |sv x| ≤ A) (hA : A < 4294967296) :
    sv (sneg x) = - sv x ∧ |- sv x| ≤ A := by
  have h1 := abs_le.1 hx
  have e : sneg x = 8589934592 - x := rfl
  refine ⟨?_, by rw [abs_neg]; exact hx⟩
  rw [e]
  unfold sv at h1 ⊢
  omega

@[expose] noncomputable def Yv (V XM e i : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 8, ((fld XM 8 (8 * i + k) : ℤ) - 128) * ((fld (fld V 128 e) 16 k : ℤ) - 7)

theorem yv_spec {V XM e : ℕ} (hVe : ∀ m < 8, fld (fld V 128 e) 16 m < 16) (i : ℕ) :
    sv (yv V XM e i) = Yv V XM e i ∧ |Yv V XM e i| ≤ 16384 := by
  have hr : ∀ k, sv (rco V e k) = (fld (fld V 128 e) 16 k : ℤ) - 7 :=
    fun k => sv_spk _ 7 (by norm_num)
  have hx : ∀ k, sv (xe XM i k) = (fld XM 8 (8 * i + k) : ℤ) - 128 :=
    fun k => sv_spk _ 128 (by norm_num)
  have hpb : ∀ k < 8, -2048 ≤ sv (xe XM i k) * sv (rco V e k) ∧
      sv (xe XM i k) * sv (rco V e k) ≤ 2048 := by
    intro k hk
    rw [hr k, hx k, mul_comm]
    exact prod_bound (hVe k hk) (fld_lt XM 8 (8 * i + k))
  have hb : ∀ k < 8, |sv (smul (xe XM i k) (rco V e k))| ≤ 2048 := by
    intro k hk
    rw [sv_smul (by linarith [(hpb k hk).1]), abs_le]
    exact hpb k hk
  obtain ⟨hsum, hbd⟩ := sv_ssum _ 2048 8 hb (by norm_num)
  have hterm : ∀ k ∈ Finset.range 8, sv (smul (xe XM i k) (rco V e k)) =
      ((fld XM 8 (8 * i + k) : ℤ) - 128) * ((fld (fld V 128 e) 16 k : ℤ) - 7) := by
    intro k hk
    rw [sv_smul (by linarith [(hpb k (Finset.mem_range.1 hk)).1]), hr k, hx k]
  rw [Finset.sum_congr rfl hterm] at hsum hbd
  have e1 : yv V XM e i = ssum 8 fun k => smul (xe XM i k) (rco V e k) := rfl
  rw [e1, hsum]
  refine ⟨rfl, ?_⟩
  unfold Yv
  push_cast at hbd
  linarith [hbd]

@[expose] def crR (a0 a1 a2 a3 b0 b1 b2 b3 : ℤ) : ℤ := a0 * b2 - a1 * b3 - (a2 * b0 - a3 * b1)

@[expose] def crI (a0 a1 a2 a3 b0 b1 b2 b3 : ℤ) : ℤ := a0 * b3 + a1 * b2 - (a2 * b1 + a3 * b0)

theorem crossK_eq {a0 a1 a2 a3 b0 b1 b2 b3 : ℕ} (k : ℕ → ℕ → Bool)
    (ha0 : |sv a0| ≤ 16384) (ha1 : |sv a1| ≤ 16384) (ha2 : |sv a2| ≤ 16384) (ha3 : |sv a3| ≤ 16384)
    (hb0 : |sv b0| ≤ 16384) (hb1 : |sv b1| ≤ 16384) (hb2 : |sv b2| ≤ 16384) (hb3 : |sv b3| ≤ 16384) :
    ∃ re im, crossK a0 a1 a2 a3 b0 b1 b2 b3 k = k re im ∧
      sv re = crR (sv a0) (sv a1) (sv a2) (sv a3) (sv b0) (sv b1) (sv b2) (sv b3) ∧
      sv im = crI (sv a0) (sv a1) (sv a2) (sv a3) (sv b0) (sv b1) (sv b2) (sv b3) ∧
      |sv re| ≤ 1073741824 ∧ |sv im| ≤ 1073741824 := by
  have m : ∀ {x y : ℕ}, |sv x| ≤ 16384 → |sv y| ≤ 16384 →
      sv (smul x y) = sv x * sv y ∧ |sv (smul x y)| ≤ 268435456 := by
    intro x y hx hy
    obtain ⟨h1, h2⟩ := sv_smul_bd hx hy (by norm_num)
    rw [h1]
    exact ⟨rfl, by linarith⟩
  have s : ∀ {x y : ℕ} {A : ℤ}, |sv x| ≤ A → |sv y| ≤ A → A < 2147483648 →
      sv (sadd x y) = sv x + sv y ∧ |sv (sadd x y)| ≤ 2 * A := by
    intro x y A hx hy hA
    obtain ⟨h1, h2⟩ := sv_sadd_bd hx hy (by linarith)
    rw [h1]
    exact ⟨rfl, by linarith⟩
  have n : ∀ {x : ℕ} {A : ℤ}, |sv x| ≤ A → A < 4294967296 →
      sv (sneg x) = - sv x ∧ |sv (sneg x)| ≤ A := by
    intro x A hx hA
    obtain ⟨h1, h2⟩ := sv_sneg_bd hx hA
    rw [h1]
    exact ⟨rfl, h2⟩
  obtain ⟨p02, q02⟩ := m ha0 hb2
  obtain ⟨p13, q13⟩ := m ha1 hb3
  obtain ⟨p20, q20⟩ := m ha2 hb0
  obtain ⟨p31, q31⟩ := m ha3 hb1
  obtain ⟨p03, q03⟩ := m ha0 hb3
  obtain ⟨p12, q12⟩ := m ha1 hb2
  obtain ⟨p21, q21⟩ := m ha2 hb1
  obtain ⟨p30, q30⟩ := m ha3 hb0
  obtain ⟨n13, r13⟩ := n q13 (by norm_num)
  obtain ⟨n31, r31⟩ := n q31 (by norm_num)
  obtain ⟨s1, t1⟩ := s q02 r13 (by norm_num)
  obtain ⟨s2, t2⟩ := s q20 r31 (by norm_num)
  obtain ⟨n2, r2⟩ := n t2 (by norm_num)
  obtain ⟨s3, t3⟩ := s t1 r2 (by norm_num)
  obtain ⟨u1, v1⟩ := s q03 q12 (by norm_num)
  obtain ⟨u2, v2⟩ := s q21 q30 (by norm_num)
  obtain ⟨m2, w2⟩ := n v2 (by norm_num)
  obtain ⟨u3, v3⟩ := s v1 w2 (by norm_num)
  have e : crossK a0 a1 a2 a3 b0 b1 b2 b3 k =
      k (sadd (sadd (smul a0 b2) (sneg (smul a1 b3))) (sneg (sadd (smul a2 b0) (sneg (smul a3 b1)))))
        (sadd (sadd (smul a0 b3) (smul a1 b2)) (sneg (sadd (smul a2 b1) (smul a3 b0)))) := by
    unfold crossK
    rw [strictB_eq, strictB_eq]
  refine ⟨_, _, e, ?_, ?_, by linarith, by linarith⟩
  · rw [s3, s1, n2, s2, p02, n13, p13, p20, n31, p31]
    unfold crR
    ring
  · rw [u3, u1, m2, u2, p03, p12, p21, p30]
    unfold crI
    ring

theorem gz_iff (x y : ℕ) : gz x y = true ↔ sv x = 0 ∧ sv y = 0 := by
  have e : gz x y = CFSG.TcRes.TK.andB (Nat.beq x 4294967296) (Nat.beq y 4294967296) := rfl
  rw [e, andB_eq_true, beq_eq_true, beq_eq_true]
  unfold sv
  omega

theorem gnorm_eq (x y : ℕ) : (gnorm x y : ℤ) = sv x ^ 2 + sv y ^ 2 := by
  have e : gnorm x y = sabs x * sabs x + sabs y * sabs y := rfl
  rw [e]
  push_cast
  rw [sabs_eq, sabs_eq]
  rw [← abs_mul, ← abs_mul, abs_mul_self, abs_mul_self]
  ring

theorem gsm_iff (x y : ℕ) : gsm x y = true ↔
    ¬ (sv x = 0 ∧ sv y = 0) ∧ (sv x ^ 2 + sv y ^ 2).natAbs ∣ 30 ^ 64 := by
  have e : gsm x y = CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (gz x y)) (smoothN (gnorm x y)) := rfl
  have hn : gnorm x y = (sv x ^ 2 + sv y ^ 2).natAbs := by
    rw [← gnorm_eq]
    rfl
  rw [e, andB_eq_true, notB_eq_true, smoothN_iff, hn, ← gz_iff]
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨by rw [h1]; exact Bool.false_ne_true, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨Bool.eq_false_iff.2 h1, ?_, h3⟩
    intro h0
    apply h1
    rw [gz_iff]
    have := Int.natAbs_eq_zero.1 h0
    constructor <;> nlinarith [sq_nonneg (sv x), sq_nonneg (sv y)]

theorem wK_eq (V XM e : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool) :
    wK V XM e k = k (yv V XM e 4) (yv V XM e 5) (yv V XM e 6) (yv V XM e 7) := by
  unfold wK
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq]

theorem boolRec_true {F T c : Bool} (h : Bool.rec (motive := fun _ => Bool) F T c = true) :
    (c = true → T = true) ∧ (c = false → F = true) := by
  cases c
  · exact ⟨fun h' => absurd h' Bool.false_ne_true, fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

@[expose] noncomputable def pbK (CMs : ℕ → ℕ) (V XM SG KE REPS e : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  fun y4 y5 y6 y7 =>
    Bool.rec (motive := fun _ => Bool)
      (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit SG e)) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (gsm y4 y5) (gsm y6 y7))
        (strictB (fld KE (nat_lit 4) e) fun k =>
          CFSG.TcRes.TK.andB (Nat.blt k (nat_lit 12)) (CFSG.TcRes.TK.andB (bit (CMs k) e)
            (strictB (fld REPS (nat_lit 8) k) fun r =>
              CFSG.TcRes.TK.andB (Nat.ble r e) (wK V XM r fun z4 z5 z6 z7 =>
                crossK y4 y5 y6 y7 z4 z5 z6 z7 gz))))))
      (bit SG e)
      (CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7))

theorem pbE_pbK {CMs : ℕ → ℕ} {V XM SG KE REPS e : ℕ} (h : pbE CMs V XM SG KE REPS e = true) :
    pbK CMs V XM SG KE REPS e (yv V XM e 4) (yv V XM e 5) (yv V XM e 6) (yv V XM e 7) = true := by
  have h1 : wK V XM e (pbK CMs V XM SG KE REPS e) = true := h
  rw [wK_eq] at h1
  exact h1

theorem pbK_spec {CMs : ℕ → ℕ} {V XM SG KE REPS e y4 y5 y6 y7 : ℕ} {Y4 Y5 Y6 Y7 : ℤ}
    (hVl : ∀ g < 240, ∀ m < 8, fld (fld V 128 g) 16 m < 16) (he : e < 240)
    (h4 : sv y4 = Y4) (h5 : sv y5 = Y5) (h6 : sv y6 = Y6) (h7 : sv y7 = Y7)
    (b4 : |Y4| ≤ 16384) (b5 : |Y5| ≤ 16384) (b6 : |Y6| ≤ 16384) (b7 : |Y7| ≤ 16384)
    (h : pbK CMs V XM SG KE REPS e y4 y5 y6 y7 = true) :
    ((Y4 = 0 ∧ Y5 = 0 ∧ Y6 = 0 ∧ Y7 = 0) ↔ SG.testBit e = true) ∧
    (SG.testBit e = false →
      ((¬ (Y4 = 0 ∧ Y5 = 0) ∧ (Y4 ^ 2 + Y5 ^ 2).natAbs ∣ 30 ^ 64) ∨
        (¬ (Y6 = 0 ∧ Y7 = 0) ∧ (Y6 ^ 2 + Y7 ^ 2).natAbs ∣ 30 ^ 64)) ∧
      fld KE 4 e < 12 ∧ (CMs (fld KE 4 e)).testBit e = true ∧ fld REPS 8 (fld KE 4 e) ≤ e ∧
      crR Y4 Y5 Y6 Y7
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 4) (Yv V XM (fld REPS 8 (fld KE 4 e)) 5)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 6) (Yv V XM (fld REPS 8 (fld KE 4 e)) 7) = 0 ∧
      crI Y4 Y5 Y6 Y7
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 4) (Yv V XM (fld REPS 8 (fld KE 4 e)) 5)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 6) (Yv V XM (fld REPS 8 (fld KE 4 e)) 7) = 0) := by
  have hy : ∀ g < 240, ∀ i, sv (yv V XM g i) = Yv V XM g i ∧ |Yv V XM g i| ≤ 16384 :=
    fun g hg i => yv_spec (hVl g hg) i
  have hb : ∀ g < 240, ∀ i, |sv (yv V XM g i)| ≤ 16384 := by
    intro g hg i
    rw [(hy g hg i).1]
    exact (hy g hg i).2
  have hb4 : |sv y4| ≤ 16384 := by rw [h4]; exact b4
  have hb5 : |sv y5| ≤ 16384 := by rw [h5]; exact b5
  have hb6 : |sv y6| ≤ 16384 := by rw [h6]; exact b6
  have hb7 : |sv y7| ≤ 16384 := by rw [h7]; exact b7
  unfold pbK at h
  obtain ⟨hT, hF⟩ := boolRec_true h
  have hF' : CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7) = false →
      bit SG e = false ∧ (gsm y4 y5 = true ∨ gsm y6 y7 = true) ∧
      fld KE 4 e < 12 ∧ bit (CMs (fld KE 4 e)) e = true ∧ fld REPS 8 (fld KE 4 e) ≤ e ∧
      crossK y4 y5 y6 y7
        (yv V XM (fld REPS 8 (fld KE 4 e)) 4) (yv V XM (fld REPS 8 (fld KE 4 e)) 5)
        (yv V XM (fld REPS 8 (fld KE 4 e)) 6) (yv V XM (fld REPS 8 (fld KE 4 e)) 7) gz = true := by
    intro hc
    obtain ⟨h1, h2⟩ := andB_eq_true.1 (hF hc)
    obtain ⟨h3, h4⟩ := andB_eq_true.1 h2
    rw [strictB_eq] at h4
    obtain ⟨h5, h6⟩ := andB_eq_true.1 h4
    obtain ⟨h7, h8⟩ := andB_eq_true.1 h6
    rw [strictB_eq] at h8
    obtain ⟨h9, h10⟩ := andB_eq_true.1 h8
    rw [wK_eq] at h10
    exact ⟨notB_eq_true.1 h1, orB_eq_true.1 h3, blt_eq_true.1 h5, h7, ble_eq_true.1 h9, h10⟩
  have hc : (Y4 = 0 ∧ Y5 = 0 ∧ Y6 = 0 ∧ Y7 = 0) ↔ CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7) = true := by
    rw [andB_eq_true, gz_iff, gz_iff, h4, h5, h6, h7, and_assoc]
  refine ⟨?_, fun hs => ?_⟩
  · rw [hc, ← bit_iff]
    cases hcv : CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7)
    · rw [(hF' hcv).1]
    · rw [hT hcv]
  have hcf : CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7) = false := by
    cases hcv : CFSG.TcRes.TK.andB (gz y4 y5) (gz y6 y7)
    · rfl
    · have h1 := bit_iff.1 (hT hcv)
      rw [hs] at h1
      exact absurd h1 (by decide)
  obtain ⟨-, hg, hk, hcm, hr, hx⟩ := hF' hcf
  have hr' : fld REPS 8 (fld KE 4 e) < 240 := lt_of_le_of_lt hr he
  obtain ⟨re, im, hk', hre, him, -, -⟩ := crossK_eq gz hb4 hb5 hb6 hb7
    (hb _ hr' 4) (hb _ hr' 5) (hb _ hr' 6) (hb _ hr' 7)
  rw [hk', gz_iff, hre, him, h4, h5, h6, h7,
    (hy _ hr' 4).1, (hy _ hr' 5).1, (hy _ hr' 6).1, (hy _ hr' 7).1] at hx
  rw [gsm_iff, gsm_iff, h4, h5, h6, h7] at hg
  exact ⟨hg, hk, bit_iff.1 hcm, hr, hx.1, hx.2⟩

theorem pbE_spec {CMs : ℕ → ℕ} {V XM SG KE REPS e : ℕ}
    (hVl : ∀ g < 240, ∀ m < 8, fld (fld V 128 g) 16 m < 16) (he : e < 240)
    (h : pbE CMs V XM SG KE REPS e = true) :
    ((Yv V XM e 4 = 0 ∧ Yv V XM e 5 = 0 ∧ Yv V XM e 6 = 0 ∧ Yv V XM e 7 = 0) ↔
      SG.testBit e = true) ∧
    (SG.testBit e = false →
      ((¬ (Yv V XM e 4 = 0 ∧ Yv V XM e 5 = 0) ∧
          (Yv V XM e 4 ^ 2 + Yv V XM e 5 ^ 2).natAbs ∣ 30 ^ 64) ∨
        (¬ (Yv V XM e 6 = 0 ∧ Yv V XM e 7 = 0) ∧
          (Yv V XM e 6 ^ 2 + Yv V XM e 7 ^ 2).natAbs ∣ 30 ^ 64)) ∧
      fld KE 4 e < 12 ∧ (CMs (fld KE 4 e)).testBit e = true ∧ fld REPS 8 (fld KE 4 e) ≤ e ∧
      crR (Yv V XM e 4) (Yv V XM e 5) (Yv V XM e 6) (Yv V XM e 7)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 4) (Yv V XM (fld REPS 8 (fld KE 4 e)) 5)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 6) (Yv V XM (fld REPS 8 (fld KE 4 e)) 7) = 0 ∧
      crI (Yv V XM e 4) (Yv V XM e 5) (Yv V XM e 6) (Yv V XM e 7)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 4) (Yv V XM (fld REPS 8 (fld KE 4 e)) 5)
        (Yv V XM (fld REPS 8 (fld KE 4 e)) 6) (Yv V XM (fld REPS 8 (fld KE 4 e)) 7) = 0) := by
  have hy := fun i => yv_spec (XM := XM) (hVl e he) i
  exact pbK_spec hVl he (hy 4).1 (hy 5).1 (hy 6).1 (hy 7).1 (hy 4).2 (hy 5).2 (hy 6).2 (hy 7).2
    (pbE_pbK h)

theorem pbW_spec {CMs : ℕ → ℕ} {V XM SG KE REPS : ℕ}
    (h : ∀ i < 4, pbW CMs V XM SG KE REPS i = true) (e : ℕ) (he : e < 240) :
    pbE CMs V XM SG KE REPS e = true := by
  have h1 := (allLt_iff _ _).1 (h (e / 60) (by omega)) (e % 60) (Nat.mod_lt _ (by norm_num))
  have e1 : Nat.add (Nat.mul 60 (e / 60)) (e % 60) = e := by
    rw [nadd, nmul]
    exact Nat.div_add_mod e 60
  beta_reduce at h1
  rw [e1] at h1
  exact h1

theorem add_eq_lor_add_land (a b : ℕ) : a + b = (a ||| b) + (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have ih' := ih (a / 2) (by omega) (b / 2)
      have h1 : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
      have h2 : (a &&& b) / 2 = a / 2 &&& b / 2 := Nat.and_div_two
      have h3 : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := Nat.or_mod_two_eq_one
      have h4 : (a &&& b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := Nat.and_mod_two_eq_one
      have e1 := Nat.div_add_mod (a ||| b) 2
      have e2 := Nat.div_add_mod (a &&& b) 2
      have e3 := Nat.div_add_mod a 2
      have e4 := Nat.div_add_mod b 2
      have p1 := Nat.mod_lt (a ||| b) (by decide : 2 > 0)
      have p2 := Nat.mod_lt (a &&& b) (by decide : 2 > 0)
      have p3 := Nat.mod_lt a (by decide : 2 > 0)
      have p4 := Nat.mod_lt b (by decide : 2 > 0)
      by_cases ha2 : a % 2 = 1 <;> by_cases hb2 : b % 2 = 1
      · have x1 := h3.2 (Or.inl ha2)
        have x2 := h4.2 ⟨ha2, hb2⟩
        omega
      · have x1 := h3.2 (Or.inl ha2)
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => hb2 (h4.1 h).2
        omega
      · have x1 := h3.2 (Or.inr hb2)
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => ha2 (h4.1 h).1
        omega
      · have x1 : (a ||| b) % 2 ≠ 1 := fun h => by rcases h3.1 h with h | h <;> contradiction
        have x2 : (a &&& b) % 2 ≠ 1 := fun h => ha2 (h4.1 h).1
        omega

theorem sumLt_succ' (c : ℕ) (f : ℕ → ℕ) : sumLt (c + 1) f = sumLt c f + f c := by
  change strictN (sumLt c f) (fun a => Nat.add a (f c)) = _
  rw [strictN_eq]
  rfl

theorem lorLt_succ (c : ℕ) (f : ℕ → ℕ) : lorLt (c + 1) f = lorLt c f ||| f c := by
  change strictN (lorLt c f) (fun a => Nat.lor a (f c)) = _
  rw [strictN_eq]
  rfl

theorem lorLt_testBit (f : ℕ → ℕ) (x : ℕ) :
    ∀ c, (lorLt c f).testBit x = true ↔ ∃ i < c, (f i).testBit x = true := by
  intro c
  induction c with
  | zero =>
    change (0 : ℕ).testBit x = true ↔ _
    simp
  | succ c ih =>
    rw [lorLt_succ, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨c, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem sum_eq_lor (f : ℕ → ℕ) :
    ∀ c, lorLt c f ≤ sumLt c f ∧ (sumLt c f = lorLt c f → ∀ x, ∀ i < c, ∀ j < c,
      (f i).testBit x = true → (f j).testBit x = true → i = j) := by
  intro c
  induction c with
  | zero =>
    refine ⟨le_of_eq rfl, fun _ x i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ c ih =>
    obtain ⟨hle, hd⟩ := ih
    have e := add_eq_lor_add_land (lorLt c f) (f c)
    rw [sumLt_succ', lorLt_succ]
    refine ⟨by omega, fun hs x i hi j hj hx hy => ?_⟩
    have h1 : sumLt c f = lorLt c f := by omega
    have h2 : lorLt c f &&& f c = 0 := by omega
    have hc : ∀ i < c, (f i).testBit x = true → (f c).testBit x = true → False := by
      intro i hi hx hy
      have h3 : (lorLt c f).testBit x = true := (lorLt_testBit f x c).2 ⟨i, hi, hx⟩
      have h4 := congrArg (fun t => t.testBit x) h2
      simp only [Nat.testBit_and, h3, hy, Bool.and_self, Nat.zero_testBit] at h4
      exact absurd h4 (by decide)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hd h1 x i hi j hj hx hy
    · exact (hc i hi hx hy).elim
    · exact (hc j hj hy hx).elim
    · rfl

theorem cls_spec {CMs : ℕ → ℕ} {V XM SG REPS : ℕ}
    (hVl : ∀ g < 240, ∀ m < 8, fld (fld V 128 g) 16 m < 16)
    (hR : ∀ k < 12, fld REPS 8 k < 240) (h : clsOK CMs V XM SG REPS = true) :
    (∀ x, (∃ k < 12, (CMs k).testBit x = true) ↔ (M240 ^^^ SG).testBit x = true) ∧
    (∀ x, ∀ i < 12, ∀ j < 12, (CMs i).testBit x = true → (CMs j).testBit x = true → i = j) ∧
    (∀ k < 12, (CMs k).testBit (fld REPS 8 k) = true) ∧
    (∀ i < 12, ∀ j < 12, i < j → fld REPS 8 i < fld REPS 8 j) ∧
    (∀ i < 12, ∀ j < 12, i < j →
      ¬ (crR (Yv V XM (fld REPS 8 i) 4) (Yv V XM (fld REPS 8 i) 5) (Yv V XM (fld REPS 8 i) 6)
            (Yv V XM (fld REPS 8 i) 7) (Yv V XM (fld REPS 8 j) 4) (Yv V XM (fld REPS 8 j) 5)
            (Yv V XM (fld REPS 8 j) 6) (Yv V XM (fld REPS 8 j) 7) = 0 ∧
          crI (Yv V XM (fld REPS 8 i) 4) (Yv V XM (fld REPS 8 i) 5) (Yv V XM (fld REPS 8 i) 6)
            (Yv V XM (fld REPS 8 i) 7) (Yv V XM (fld REPS 8 j) 4) (Yv V XM (fld REPS 8 j) 5)
            (Yv V XM (fld REPS 8 j) 6) (Yv V XM (fld REPS 8 j) 7) = 0) ∧
      ((crR (Yv V XM (fld REPS 8 i) 4) (Yv V XM (fld REPS 8 i) 5) (Yv V XM (fld REPS 8 i) 6)
            (Yv V XM (fld REPS 8 i) 7) (Yv V XM (fld REPS 8 j) 4) (Yv V XM (fld REPS 8 j) 5)
            (Yv V XM (fld REPS 8 j) 6) (Yv V XM (fld REPS 8 j) 7)) ^ 2 +
        (crI (Yv V XM (fld REPS 8 i) 4) (Yv V XM (fld REPS 8 i) 5) (Yv V XM (fld REPS 8 i) 6)
            (Yv V XM (fld REPS 8 i) 7) (Yv V XM (fld REPS 8 j) 4) (Yv V XM (fld REPS 8 j) 5)
            (Yv V XM (fld REPS 8 j) 6) (Yv V XM (fld REPS 8 j) 7)) ^ 2).natAbs ∣ 30 ^ 64) := by
  unfold clsOK at h
  rw [strictB_eq] at h
  obtain ⟨hs, h⟩ := andB_eq_true.1 h
  obtain ⟨hl, h⟩ := andB_eq_true.1 h
  obtain ⟨hm, h⟩ := andB_eq_true.1 h
  obtain ⟨hi, hx⟩ := andB_eq_true.1 h
  rw [beq_eq_true, nxor] at hs hl
  have hm' := (allLt_iff _ _).1 hm
  have hi' := (allLt_iff _ _).1 hi
  have hx' := (allLt_iff _ _).1 hx
  have hmono' : ∀ j, j < 12 → ∀ i, i < j → fld REPS 8 i < fld REPS 8 j := by
    intro j
    induction j with
    | zero => exact fun _ i hij => absurd hij (Nat.not_lt_zero _)
    | succ j ih =>
      intro hj i hij
      have hs' := blt_eq_true.1 (hi' j (by omega : j < 11))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact lt_trans (ih (by omega) i hij) hs'
      · exact hs'
  have hmono : ∀ i j, j < 12 → i < j → fld REPS 8 i < fld REPS 8 j :=
    fun i j hj hij => hmono' j hj i hij
  refine ⟨fun x => ?_, fun x i hi j hj => (sum_eq_lor CMs 12).2 (by rw [hs, hl]) x i hi j hj,
    fun k hk => bit_iff.1 (hm' k hk), fun i _ j hj hij => hmono i j hj hij,
    fun i hi j hj hij => ?_⟩
  · rw [← hl, lorLt_testBit]
  have hy := fun g (hg : g < 240) i => yv_spec (XM := XM) (hVl g hg) i
  have hb : ∀ g < 240, ∀ i, |sv (yv V XM g i)| ≤ 16384 := by
    intro g hg i
    rw [(hy g hg i).1]
    exact (hy g hg i).2
  have h1 := (allLt_iff _ _).1 (hx' i hi) j hj
  rw [orB_eq_true, ble_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by omega)
  rw [wK_eq, wK_eq] at h1
  have ri := hR i hi
  have rj := hR j hj
  obtain ⟨re, im, hk', hre, him, -, -⟩ := crossK_eq gsm (hb _ ri 4) (hb _ ri 5) (hb _ ri 6)
    (hb _ ri 7) (hb _ rj 4) (hb _ rj 5) (hb _ rj 6) (hb _ rj 7)
  rw [hk', gsm_iff, hre, him, (hy _ ri 4).1, (hy _ ri 5).1, (hy _ ri 6).1, (hy _ ri 7).1,
    (hy _ rj 4).1, (hy _ rj 5).1, (hy _ rj 6).1, (hy _ rj 7).1] at h1
  exact h1

section Lines

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus Certificates.TcRes

theorem lnK_spec
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {neg : ℕ → ℕ}
    {ADJ POS DEC V X Y PW : ℕ} {RTs QS MVS : ℕ → ℕ} {cr Φ g0 lp : ℕ} (hvec : vec = vecOf 8 V)
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v)
      (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hX : ∀ v < 240, ∀ g < 240, (CFSG.TcRes.TK.dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hpos : ∀ g < 240, pos8OK V POS g = true) (hdec : ∀ g < 240, dec8OK QS MVS V POS DEC g = true)
    (hph : ∀ g < 240, fld PW 8 g < 240)
    (hΦsub : ∀ a ∈ mset 240 Φ, ∀ b ∈ mset 240 Φ, ∀ c < 240, vec c = vec a - vec b →
      c ∈ mset 240 Φ)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (h : lnK ADJ POS DEC PW cr Φ g0 lp = true) :
    ∃ r0, CompRaw vec (fun g v => fld (RTs g) 8 v) (fun g => fld PW 8 g) 240 (mset 240 Φ)
        (mset 240 (Nat.land lp M240)) g0 (Nat.shiftRight lp 240) r0 ∧
      dKs (Nat.shiftRight lp 240) = ksOf (dR (Nat.shiftRight lp 240)) (CFSG.TcRes.TK.dN (Nat.shiftRight lp 240)) := by
  obtain ⟨ψ, d, r0, hk, hc, hks⟩ := compRaw_of_crK8 hvec hD hX hq hmv hpos hdec hph hΦsub hVl hYc
    hYl hQb h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 hk
  rw [beq_eq_true] at h1 h2
  subst h1 h2
  exact ⟨r0, hc, hks⟩

theorem lnJ_spec {RTs LCs LPs : ℕ → ℕ} {ADJ POS DEC NEG PW COLS SG : ℕ}
    (h : lnJ RTs LCs LPs ADJ POS DEC NEG PW COLS SG = true) :
    lnK ADJ POS DEC PW (LCs 12) SG (fld COLS 8 0) (LPs 12) = true ∧
      Nat.land (LPs 12) M240 = sMask RTs NEG (fld COLS 8 0) (fld COLS 8 2) := by
  unfold lnJ at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  exact ⟨h1, beq_eq_true.1 h2⟩

theorem splitF_eq {l : TcrLab} (hl : l.r < 16) : splitF (tkLab l) = tcrSplitFree l := by
  obtain ⟨a1, -, a3⟩ := tkLab_dec hl
  rw [splitF, strictB_eq, strictB_eq, a1, a3]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tcrSplitFree, tcrUntw, untw, tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq,
    nble_eq, nmod_eq] <;> tauto

theorem halfF_eq {l : TcrLab} (hl : l.r < 16) : halfF (tkLab l) = tcrHalfFree l := by
  obtain ⟨a1, a2, a3⟩ := tkLab_dec hl
  rw [halfF, strictB_eq, strictB_eq, strictB_eq, a1, a2, a3, tcrHalfFree, ← splitF_eq hl]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq, nmod_eq] <;> tauto

theorem jok3_spec {LPs : ℕ → ℕ} (h : jok3 LPs = true) :
    ∀ x < 13, Nat.land (LPs x) M240 ≠ Nat.land (LPs 12) M240 →
      (tcrLabsOf (tkCd5 (Nat.shiftRight (LPs x) 240)) 1).any tcrSplitFree = true →
      (∀ y < 13, y ≠ x →
        (tcrLabsOf (tkCd5 (Nat.shiftRight (LPs y) 240)) 1).any
          (fun l => (tcrLabsOf (tkCd5 (Nat.shiftRight (LPs 12) 240)) 1).contains l) = true ∨
        (tcrLabsOf (tkCd5 (Nat.shiftRight (LPs y) 240)) 1).any tcrHalfFree = true) → False := by
  intro x hx hps hsp hoth
  unfold jok3 at h
  rw [strictB_eq, strictB_eq] at h
  have hX := (allLt_iff _ _).1 h x hx
  simp only [jok3X, notB_eq, andB_eq, orB_eq, nbeq_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff] at hX
  rcases hX with hX | hX | hX
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hX
    exact hps hX
  · rw [anyLabK_eq splitF tcrSplitFree (fun l hl => splitF_eq hl) _ _ (by norm_num), hsp] at hX
    exact Bool.false_ne_true hX.symm
  · have : allLt 13 (fun y => decide (y = x) ||
        (anyLabK halfF (Nat.shiftRight (LPs y) 240) 1 ||
          meetsK (Nat.shiftRight (LPs y) 240) (Nat.shiftRight (LPs 12) 240) 1)) = true := by
      rw [allLt_iff]
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · rw [anyLabK_eq halfF tcrHalfFree (fun l hl => halfF_eq hl) _ _ (by norm_num),
          meetsK_eq _ _ _ (by norm_num)]
        rcases hoth y hy hyx with h1 | h1 <;> simp only [h1, Bool.or_true, Bool.true_or]
    rw [this] at hX
    exact Bool.false_ne_true hX.symm

end Lines

end CFSG.KC.TcRes

end
