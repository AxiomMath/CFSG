module

public import Certificates.Data.Kernel.SporSch.HNXDot
public import CFSG.Certificates.Kernel.SporSch.HNXPtSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld

set_option maxRecDepth 100000
set_option exponentiation.threshold 2200

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord CFSG.KS.PackFld
open Finset Matrix

theorem dot_fld_xor {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ^^^ B) (fun i => g i ^^^ h i) := by
  intro i k hk
  rw [Nat.testBit_xor, hA i k hk, hB i k hk, Nat.testBit_xor]

theorem dot_fld_shl {w X s : Nat} {g : Nat → Nat} (hX : Fld w X g) (hs : s < w)
    (hg : ∀ i, g i <<< s < 2 ^ w) : Fld w (X <<< s) (fun i => g i <<< s) := by
  intro i k hk
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases hks : s ≤ k
  · have e : w * i + k - s = w * i + (k - s) := by omega
    have hik : w * i + k ≥ s := by omega
    rw [e, hX i (k - s) (by omega)]
    simp [hks, hik]
  · have hr : (decide (k ≥ s) && (g i).testBit (k - s)) = false := by
      have : ¬ k ≥ s := hks
      simp [this]
    rw [hr]
    by_cases hi : w * i + k ≥ s
    · have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h
          omega
        · exact h
      have hwi : w * i = w * (i - 1) + w := by
        have e1 : i = (i - 1) + 1 := by omega
        conv_lhs => rw [e1]
        rw [Nat.mul_add, Nat.mul_one]
      have e : w * i + k - s = w * (i - 1) + (w + k - s) := by omega
      rw [e, hX (i - 1) (w + k - s) (by omega)]
      have h1 := Nat.testBit_lt_two_pow (i := w + k) (Nat.lt_of_lt_of_le (hg (i - 1))
        (Nat.pow_le_pow_right (by omega) (by omega)))
      have hwk : w + k ≥ s := by omega
      rw [Nat.testBit_shiftLeft] at h1
      simp only [hwk, decide_true, Bool.true_and] at h1
      simp [hi, h1]
    · simp [hi]

theorem dot_le_or (a b : Nat) : b ≤ a ||| b := by
  have h : (a ||| b) &&& b = b := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_or]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  calc b = (a ||| b) &&& b := h.symm
    _ ≤ a ||| b := Nat.and_le_left

theorem dot_rec_or (w : Nat) {f : Nat → Nat} (hf : ∀ r, f r < 2 ^ w) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (f r) (Nat.mul w r))) n = pk w n f
  | 0 => rfl
  | n + 1 => by
    change Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (f r) (Nat.mul w r))) n ||| f n <<< (w * n) = _
    rw [dot_rec_or w hf n, pk_succ, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt
      (pk_lt (fun t _ => hf t)), Nat.shiftLeft_eq, Nat.add_comm]

theorem bit_mod (x t : Nat) : (x / 2 ^ t % 2).testBit 0 = x.testBit t := by
  have h := Nat.testBit_div_two_pow (n := t) x 0
  rw [Nat.zero_add] at h
  rw [← h, Nat.testBit_zero, Nat.testBit_zero, Nat.mod_mod]

theorem spread_P_le (e : Nat) : spread_P e 133 ≤ 1729 := by
  unfold spread_P
  have : 133 / 2 ^ e * 2 ^ e ≤ 133 := Nat.div_mul_le_self _ _
  omega

theorem spread_V_lt1729 (e : Nat) (f : Nat → Nat) (hf : ∀ j, f j < 8) :
    spread_V (spread_P e) f 133 < 2 ^ 1729 :=
  Nat.lt_of_lt_of_le (spread_V_lt _ f (spread_P_sep e) hf 133)
    (Nat.pow_le_pow_right (by omega) (spread_P_le e))

noncomputable def rdig (a : Nat → Nat) (r j : Nat) : Nat := a r / 2 ^ (3 * j) % 8

theorem rdig_lt (a : Nat → Nat) (r j : Nat) : rdig a r j < 8 := Nat.mod_lt _ (by omega)

theorem mr_rec (MS MR REP n : Nat)
    (h : (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (fldW MR (Nat.mul (nat_lit 110656) i) (nat_lit 110656))
        (Nat.mul (fldW MS (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) REP), ih)) n : Bool) = true) :
    ∀ i < n, fldW MR (110656 * i) 110656 = fldW MS (1729 * i) 1729 * REP := by
  revert h
  refine spread_rec_inv _ _
    (fun n a => a = true → ∀ i < n, fldW MR (110656 * i) 110656 = fldW MS (1729 * i) 1729 * REP)
    (fun _ i hi => by omega) ?_ n
  intro n a ih h
  obtain ⟨h1, h2⟩ := spread_bAnd h
  intro i hi
  rcases Nat.lt_or_ge i n with hi' | hi'
  · exact ih h1 i hi'
  · have : i = n := by omega
    subst this
    exact Nat.eq_of_beq_eq_true h2

theorem consts_dot {MS REP ONES L1 MR : Nat} (h : dotConstsOK MS REP ONES L1 MR = true) :
    REP = pk 1729 64 (fun _ => 1) ∧ ONES = pk 13 133 (fun _ => 1) ∧ L1 = ONES * REP ∧
      ∀ i < 8, fldW MR (110656 * i) 110656 = fldW MS (1729 * i) 1729 * REP := by
  unfold dotConstsOK at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨(Nat.eq_of_beq_eq_true h1).trans (dot_rec_or 1729 (f := fun _ => 1)
      (fun _ => Nat.one_lt_two_pow (by omega)) 64),
    (Nat.eq_of_beq_eq_true h2).trans (dot_rec_or 13 (f := fun _ => 1)
      (fun _ => Nat.one_lt_two_pow (by omega)) 133), Nat.eq_of_beq_eq_true h3, ?_⟩
  exact mr_rec MS MR REP 8 h

theorem spreadR_fld {MS REP ONES L1 MR : Nat} (hm : masksOK MS = true)
    (hd : dotConstsOK MS REP ONES L1 MR = true) {a : Nat → Nat} (ha : ∀ r < 64, a r < 2 ^ 399) :
    Fld 1729 (spreadR MR (pk 1729 64 a)) (fun r => if r < 64 then
      spread_V (fun j => 13 * j) (rdig a r) 133 else 0) := by
  obtain ⟨hREP, -, -, hMR⟩ := consts_dot hd
  have key : ∀ k ≤ 8, Fld 1729 (Nat.rec (motive := fun _ => Nat) (pk 1729 64 a)
      (fun i acc => CFSG.KC.Loop.strictN acc (fun x => sp1 x (fldW MR (Nat.mul (nat_lit 110656) i)
        (nat_lit 110656)) (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i)))))
      k) (fun r => if r < 64 then spread_V (spread_P (8 - k)) (rdig a r) 133 else 0) := by
    refine spread_rec_inv _ _ (fun k x => k ≤ 8 → Fld 1729 x (fun r => if r < 64 then
      spread_V (spread_P (8 - k)) (rdig a r) 133 else 0)) (fun _ => ?_) ?_
    · refine fld_congr (fld_pk (fun t ht => Nat.lt_of_lt_of_le (ha t ht)
        (Nat.pow_le_pow_right (by omega) (by omega)))) fun r => ?_
      by_cases hr : r < 64
      · simp only [hr, ↓reduceIte]
        exact spread_init (ha r hr)
      · simp only [hr, ↓reduceIte]
    · intro k x ih hk
      have hx := ih (by omega)
      beta_reduce
      rw [loopStrictN_eq]
      unfold sp1
      rw [loopStrictN_eq]
      have hmk : fldW MR (Nat.mul 110656 k) 110656 =
          pk 1729 64 (fun _ => spread_V (spread_P (7 - k + 1)) (spread_g (7 - k)) 133) := by
        change fldW MR (110656 * k) 110656 = _
        rw [hMR k (by omega), spread_masks hm k (by omega), spread_maskB k, hREP, Nat.mul_comm,
          pk_mul]
        exact pk_congr fun t _ => Nat.one_mul _
      have hM := fld_pk (w := 1729) (n := 64)
        (g := fun _ => spread_V (spread_P (7 - k + 1)) (spread_g (7 - k)) 133)
        (fun _ _ => spread_V_lt1729 _ _ (spread_g_lt _))
      rw [← hmk] at hM
      have e8 : 8 - k = 7 - k + 1 := by omega
      have e8' : 8 - (k + 1) = 7 - k := by omega
      rw [e8] at hx
      rw [e8']
      have hs : Nat.mul 10 (Nat.shiftLeft 1 (Nat.sub 7 k)) = 10 * 2 ^ (7 - k) := by
        change 10 * (1 <<< (7 - k)) = _
        rw [Nat.one_shiftLeft]
      rw [hs]
      have hA := fld_and hx hM
      have hstep : ∀ r, ((if r < 64 then spread_V (spread_P (7 - k + 1)) (rdig a r) 133 else 0) &&&
          (if r < 64 then spread_V (spread_P (7 - k + 1)) (spread_g (7 - k)) 133 else 0)) <<<
          (10 * 2 ^ (7 - k)) < 2 ^ 1729 := by
        intro r
        by_cases hr : r < 64
        · simp only [hr, ↓reduceIte]
          have e := spread_step (7 - k) (rdig a r) (rdig_lt a r) 133
          refine Nat.lt_of_le_of_lt ?_ (spread_V_lt1729 (7 - k) _ (rdig_lt a r))
          rw [← e]
          exact dot_le_or _ _
        · simp [hr]
      have h10 : 10 * 2 ^ (7 - k) < 1729 := by
        have : 2 ^ (7 - k) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hsh := dot_fld_shl hA h10 hstep
      refine fld_congr (fld_or (dot_fld_xor hx hA) hsh) fun r => ?_
      by_cases hr : r < 64
      · simp only [hr, ↓reduceIte]
        exact spread_step (7 - k) (rdig a r) (rdig_lt a r) 133
      · simp [hr]
  have h8 := key 8 le_rfl
  rw [Nat.sub_self, spread_P_zero] at h8
  exact h8

noncomputable def dgt (a : Nat → Nat) (u : Nat) : Nat :=
  if u / 133 < 64 then rdig a (u / 133) (u % 133) else 0

theorem dgt_lt (a : Nat → Nat) (u : Nat) : dgt a u < 8 := by
  unfold dgt
  split
  · exact rdig_lt _ _ _
  · omega

theorem spreadR_lane {MS REP ONES L1 MR : Nat} (hm : masksOK MS = true)
    (hd : dotConstsOK MS REP ONES L1 MR = true) {a : Nat → Nat} (ha : ∀ r < 64, a r < 2 ^ 399) :
    Fld 13 (spreadR MR (pk 1729 64 a)) (dgt a) := by
  have hF := spreadR_fld hm hd ha
  intro u k hk
  have e : 13 * u + k = 1729 * (u / 133) + (13 * (u % 133) + k) := by omega
  rw [e, hF _ _ (by omega)]
  unfold dgt
  by_cases hr : u / 133 < 64
  · simp only [hr, ↓reduceIte]
    have hx := spread_extract (rdig a (u / 133)) (rdig_lt a _) 133 (u % 133)
      (Nat.mod_lt _ (by omega))
    rw [← hx, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [hk, Nat.add_comm]
  · simp [hr]

theorem fld_L1 {ONES REP : Nat} (hR : REP = pk 1729 64 (fun _ => 1))
    (hO : ONES = pk 13 133 (fun _ => 1)) :
    Fld 13 (ONES * REP) (fun u => if u < 8512 then 1 else 0) := by
  have e : ONES * REP = pk 13 8512 (fun _ => 1) := by
    have e0 : (8512 : Nat) = 133 * 64 := rfl
    rw [hR, hO, e0, pk_rows]
    unfold pk
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : 13 * (133 * i + j) = 13 * j + 1729 * i := by ring
    rw [e1, Nat.pow_add]
    ring
  rw [e]
  exact fld_pk (fun _ _ => Nat.one_lt_two_pow (by omega))

theorem selBit_pk {S L1 : Nat} {d : Nat → Nat} (hS : Fld 13 S d)
    (hL : Fld 13 L1 (fun u => if u < 8512 then 1 else 0)) {t : Nat} (ht : t < 13) :
    Nat.land (Nat.shiftRight S t) L1 = pk 13 8512 (fun u => d u / 2 ^ t % 2) := by
  refine pk_of_fld (by omega) (fun u k hk => ?_) (fun u _ => Nat.lt_of_lt_of_le (Nat.mod_lt _
    (by omega)) (by norm_num))
  change (S >>> t &&& L1).testBit (13 * u + k) = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, hL u k hk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [Nat.add_zero, Nat.add_comm, hS u t ht]
    by_cases hu : u < 8512
    · simp only [hu, ↓reduceIte]
      rw [bit_mod]
      simp
    · simp [hu]
  · have h1 : (if u < 8512 then 1 else 0 : Nat).testBit k = false := by
      split
      · exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      · simp
    rw [h1, Bool.and_false]
    beta_reduce
    split
    · exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega))
        (Nat.pow_le_pow_right (by omega) hk0))).symm
    · simp

theorem selT_pk {Y S L1 : Nat} {y d : Nat → Nat} (hY : Y = pk 13 8512 y) (hy : ∀ u, y u < 5)
    (hS : Fld 13 S d) (hL : Fld 13 L1 (fun u => if u < 8512 then 1 else 0)) {t : Nat}
    (ht : t < 13) : selT Y S L1 t = pk 13 8512 (fun u => d u / 2 ^ t % 2 * y u * 2 ^ t) := by
  have two : (2 : Nat) > 0 := by omega
  have m13 : (8191 : Nat) = 2 ^ 13 - 1 := rfl
  have hz : ∀ u, d u / 2 ^ t % 2 * 8191 < 2 ^ 13 := fun u => by
    have := Nat.mod_lt (d u / 2 ^ t) two
    have : d u / 2 ^ t % 2 * 8191 ≤ 1 * 8191 := Nat.mul_le_mul_right _ (by omega)
    have h13 : (2 : Nat) ^ 13 = 8192 := by norm_num
    omega
  have hy' : ∀ u, y u < 2 ^ 13 := fun u => Nat.lt_of_lt_of_le (hy u) (by norm_num)
  have hA := fld_and (fld_pk (w := 13) (n := 8512) (fun u _ => hy' u))
    (fld_pk (w := 13) (n := 8512) (fun u _ => hz u))
  have e : pk 13 8512 y &&& pk 13 8512 (fun u => d u / 2 ^ t % 2 * 8191) =
      pk 13 8512 (fun u => d u / 2 ^ t % 2 * y u) := by
    refine pk_of_fld (by omega) (fld_congr hA fun u => ?_) (fun u _ => ?_)
    · by_cases hu : u < 8512
      · simp only [hu, ↓reduceIte]
        rcases Nat.mod_two_eq_zero_or_one (d u / 2 ^ t) with h | h
        · rw [h]
          simp
        · rw [h, Nat.one_mul, Nat.one_mul, m13, Nat.and_two_pow_sub_one_eq_mod,
            Nat.mod_eq_of_lt (hy' u)]
      · simp [hu]
    · have := Nat.mod_lt (d u / 2 ^ t) two
      have := hy u
      have : d u / 2 ^ t % 2 * y u ≤ 1 * 4 := Nat.mul_le_mul (by omega) (by omega)
      have h13 : (2 : Nat) ^ 13 = 8192 := by norm_num
      omega
  unfold selT
  rw [selBit_pk hS hL ht, hY]
  change (pk 13 8512 y &&& pk 13 8512 (fun u => d u / 2 ^ t % 2) * 8191) <<< t = _
  rw [pk_mul, e, Nat.shiftLeft_eq, pk_mul]

theorem sel3_pk {Y S L1 : Nat} {y d : Nat → Nat} (hY : Y = pk 13 8512 y) (hy : ∀ u, y u < 5)
    (hS : Fld 13 S d) (hd : ∀ u, d u < 8)
    (hL : Fld 13 L1 (fun u => if u < 8512 then 1 else 0)) :
    Nat.add (selT Y S L1 (nat_lit 0)) (Nat.add (selT Y S L1 (nat_lit 1)) (selT Y S L1 (nat_lit 2)))
      = pk 13 8512 (fun u => y u * d u) := by
  change selT Y S L1 0 + (selT Y S L1 1 + selT Y S L1 2) = _
  rw [selT_pk hY hy hS hL (by omega), selT_pk hY hy hS hL (by omega),
    selT_pk hY hy hS hL (by omega), pk_add, pk_add]
  refine pk_congr fun u _ => ?_
  have h8 := hd u
  have e : d u = d u % 2 * 1 + (d u / 2 % 2 * 2 + d u / 4 % 2 * 4) := by omega
  have p4 : (2 : Nat) ^ 2 = 4 := rfl
  simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one, p4]
  conv_rhs => rw [e]
  ring

theorem ones_lane {e : Nat → Nat} (he : ∀ u, e u ≤ 28) {r : Nat} (hr : r < 64) :
    pk 13 8512 e * pk 13 133 (fun _ => 1) / 2 ^ (1729 * r + 1716) % 2 ^ 13 =
      ∑ l ∈ range 133, e (133 * r + l) := by
  let p : Nat → Nat := fun m => ∑ k ∈ range 133, if k ≤ m ∧ m - k < 8512 then e (m - k) else 0
  have hp : ∀ m, p m ≤ 3724 := fun m => by
    calc p m ≤ ∑ _k ∈ range 133, 28 := Finset.sum_le_sum fun k _ => by
            split
            · exact he _
            · omega
      _ = 3724 := by simp
  have hshift : ∀ k < 133, pk 13 8512 e * 2 ^ (13 * k) = pk 13 (8512 + 133)
      (fun m => if k ≤ m ∧ m - k < 8512 then e (m - k) else 0) := by
    intro k hk
    unfold pk
    have e1 : 8512 + 133 = k + 8512 + (133 - k) := by omega
    rw [Finset.sum_mul, e1, Finset.sum_range_add, Finset.sum_range_add]
    have z1 : ∑ x ∈ range k, (if k ≤ x ∧ x - k < 8512 then e (x - k) else 0) * 2 ^ (13 * x) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have hx' := Finset.mem_range.1 hx
        have hc : ¬ (k ≤ x ∧ x - k < 8512) := by omega
        rw [if_neg hc, Nat.zero_mul]
    have z2 : ∑ x ∈ range (133 - k), (if k ≤ k + 8512 + x ∧ k + 8512 + x - k < 8512 then
        e (k + 8512 + x - k) else 0) * 2 ^ (13 * (k + 8512 + x)) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        have hc : ¬ (k ≤ k + 8512 + x ∧ k + 8512 + x - k < 8512) := by omega
        rw [if_neg hc, Nat.zero_mul]
    rw [z1, z2, Nat.zero_add, Nat.add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.1 hu
    have hc : k ≤ k + u ∧ k + u - k < 8512 := by omega
    have hku : k + u - k = u := by omega
    beta_reduce
    rw [if_pos hc, hku, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    ring
  have hP : pk 13 8512 e * pk 13 133 (fun _ => 1) = pk 13 (8512 + 133) p := by
    have e1 : pk 13 8512 e * pk 13 133 (fun _ => 1) =
        ∑ k ∈ range 133, pk 13 8512 e * 2 ^ (13 * k) := by
      conv_lhs => unfold pk
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.one_mul]
      rfl
    rw [e1, Finset.sum_congr rfl fun k hk => hshift k (Finset.mem_range.1 hk)]
    unfold pk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul]
  have e2 : 1729 * r + 1716 = 13 * (133 * r + 132) := by ring
  have hl := lane_pk (w := 13) (n := 8512 + 133) (g := p) (fun m _ => Nat.lt_of_le_of_lt (hp m)
    (by norm_num)) (s := 133 * r + 132) (by omega)
  unfold lane at hl
  rw [hP, e2, hl]
  change ∑ k ∈ range 133, (if k ≤ 133 * r + 132 ∧ 133 * r + 132 - k < 8512 then
    e (133 * r + 132 - k) else 0) = _
  rw [← Finset.sum_range_reflect (fun l => e (133 * r + l)) 133]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hc : k ≤ 133 * r + 132 ∧ 133 * r + 132 - k < 8512 := by omega
  beta_reduce
  have hk2 : 133 * r + 132 - k = 133 * r + (133 - 1 - k) := by omega
  rw [if_pos hc, hk2]

theorem cntRows_eq (P v : Nat) : ∀ c, cntRows P v c =
    ((range c).filter fun r => fldW P (1729 * r + 1716) 13 % 5 = v).card
  | 0 => rfl
  | c + 1 => by
    change Nat.add (cntRows P v c) (Bool.rec (motive := fun _ => Nat) 0 1
      (Nat.beq (fldW P (1729 * c + 1716) 13 % 5) v)) = _
    rw [cntRows_eq P v c, Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    cases hb : Nat.beq (fldW P (1729 * c + 1716) 13 % 5) v
    · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
      rfl
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
      rfl

theorem mulC_pk {CM3 M A G : Nat} (hc : constsOK CM3 M = true) {a : Nat → Nat}
    (hA : A = pk 1729 64 a) (ha : ∀ r < 64, a r < 2 ^ 399) {g : Nat → Nat → Nat}
    (hG : G = ∑ k ∈ range 133, ∑ l ∈ range 133, g k l * 2 ^ (1729 * k + 13 * l))
    (hg : ∀ k < 133, ∀ l < 133, g k l < 5) :
    mulC CM3 A G =
      pk 13 8512 (fun u => (∑ k ∈ range 133, rdig a (u / 133) k * g k (u % 133)) % 5) := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, hRM, -⟩ := consts_facts CFSG.KD.OrdHN.consts
  have hg' : ∀ k < 133, ∀ l < 133, g k l < 2 ^ 13 := fun k hk l hl =>
    Nat.lt_of_lt_of_le (hg k hk l hl) (by norm_num)
  have hU : ∑ k ∈ range 133, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& (2 ^ (13 * 133) - 1))
      = ∑ u ∈ range (133 * 133), (if u / 133 < 64 then
        ∑ k ∈ range 133, (a (u / 133) / 2 ^ (3 * k) % 8) * g k (u % 133) else 0) * 2 ^ (13 * u) := by
    rw [← lanes_U (fun k r => a r / 2 ^ (3 * k) % 8) g]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [lanes_col hc hA ha (Finset.mem_range.1 hk), lanes_rowG hG hg' (Finset.mem_range.1 hk)]
  have hFb : ∀ t < 133 * 133, (if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) ≤ 3724 := by
    intro t _
    split
    · exact lanes_F_le hg _ _ (Nat.mod_lt _ (by omega))
    · omega
  have hR := redP_pk (w := 13) (n := 133 * 133) (p := 5) (T := 9)
    (f := fun t => if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) (by omega) hT
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
  unfold pk at hR hL hH
  beta_reduce at hR hL hH
  have hrec := lanes_mulC_rec A G CM3 CFSG.KD.OrdHN.RM (nat_lit 133)
  unfold mulC
  rw [hrec, hRM, hU, hL, hH, hR]
  unfold pk
  have e1 : 133 * 133 = 8512 + 9177 := by norm_num
  rw [e1, Finset.sum_range_add]
  have z : ∑ x ∈ range 9177, (if (8512 + x) / 133 < 64 then
      ∑ k ∈ range 133, (a ((8512 + x) / 133) / 2 ^ (3 * k) % 8) * g k ((8512 + x) % 133) else 0) % 5
      * 2 ^ (13 * (8512 + x)) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      have hc : ¬ ((8512 + x) / 133 < 64) := by omega
      rw [if_neg hc]
      simp
  rw [z, Nat.add_zero]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hc : u / 133 < 64 := by have := Finset.mem_range.1 hu; omega
  rw [if_pos hc]
  rfl

noncomputable def yD (a : Nat → Nat) (G u : Nat) : Nat :=
  (∑ k ∈ range 133, rdig a (u / 133) k * ent13 G k (u % 133)) % 5

noncomputable def rowA (L c r : Nat) : Nat := if r < c then L / 2 ^ (464 * r) % 2 ^ 399 else 0

theorem quad_cast (x : Nat → Nat) (G : Nat) :
    ((∑ l ∈ range 133, (∑ k ∈ range 133, x k * ent13 G k l) % 5 * x l : Nat) : ZMod 5) =
      (fun j : Fin 133 => ((x j.val : Nat) : ZMod 5)) ⬝ᵥ
        (ordMat 5 133 13 1729 G *ᵥ fun j : Fin 133 => ((x j.val : Nat) : ZMod 5)) := by
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod]
  simp only [dotProduct, mulVec, Finset.sum_range]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [ordMat, ent13]
  ring

end CFSG.KS.SporSch.HNXP

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord CFSG.KS.PackFld Finset Matrix

theorem dotLeaf_eq {T : Nat → Nat} {CM3 M MS REP ONES L1 MR G v : Nat} (hc : constsOK CM3 M = true)
    (hm : masksOK MS = true) (hd : dotConstsOK MS REP ONES L1 MR = true) (hG : Canon 5 133 13 G)
    (hv : v < 5) {b c : Nat} (hc64 : c ≤ 64) :
    dotLeaf T CM3 M MR L1 ONES G v b c = ((range c).filter fun r =>
      xvec T (64 * b + r) ⬝ᵥ (ordMat 5 133 13 1729 G *ᵥ xvec T (64 * b + r)) = (v : ZMod 5)).card := by
  obtain ⟨hREP, hONES, hL1, -⟩ := consts_dot hd
  have ha : ∀ r < 64, rowA (T b) c r < 2 ^ 399 := fun r _ => by
    unfold rowA
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · exact Nat.two_pow_pos _
  have hA : leafA (T b) 464 c M = pk 1729 64 (rowA (T b) c) := leafA_eq hc (T b) c hc64
  have hy : ∀ u, yD (rowA (T b) c) G u < 5 := fun u => Nat.mod_lt _ (by omega)
  have hY : mulC CM3 (pk 1729 64 (rowA (T b) c)) G = pk 13 8512 (yD (rowA (T b) c) G) :=
    mulC_pk hc rfl ha (lanes_canon_eq hG.1) (canon_ent hG)
  have hS := spreadR_lane hm hd ha
  have hL : Fld 13 L1 (fun u => if u < 8512 then 1 else 0) := by
    rw [hL1]
    exact fld_L1 hREP hONES
  have hE := sel3_pk hY hy hS (dgt_lt _) hL
  unfold dotLeaf
  simp only [strictN_eq']
  rw [hA, hE, cntRows_eq]
  refine congrArg Finset.card (Finset.filter_congr fun r hr => ?_)
  have hr' : r < c := Finset.mem_range.1 hr
  have hr64 : r < 64 := by omega
  have he : ∀ u, yD (rowA (T b) c) G u * dgt (rowA (T b) c) u ≤ 28 := fun u => by
    have h1 := hy u
    have h2 := dgt_lt (rowA (T b) c) u
    have : yD (rowA (T b) c) G u * dgt (rowA (T b) c) u ≤ 4 * 7 := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [fldW_eq, hONES]
  change pk 13 8512 (fun u => yD (rowA (T b) c) G u * dgt (rowA (T b) c) u) * pk 13 133 (fun _ => 1)
    / 2 ^ (1729 * r + 1716) % 2 ^ 13 % 5 = v ↔ _
  rw [ones_lane he hr64]
  have hrow : rowA (T b) c r = xv T (64 * b + r) := by
    unfold rowA
    rw [if_pos hr', xv_leaf T b r hr64]
  have hdk : ∀ k, rdig (rowA (T b) c) r k = xe T (64 * b + r) k := fun k => by
    unfold rdig xe
    rw [hrow]
  have hsum : ∑ l ∈ range 133, yD (rowA (T b) c) G (133 * r + l) * dgt (rowA (T b) c) (133 * r + l) =
      ∑ l ∈ range 133, (∑ k ∈ range 133, xe T (64 * b + r) k * ent13 G k l) % 5 *
        xe T (64 * b + r) l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    have e1 : (133 * r + l) / 133 = r := by omega
    have e2 : (133 * r + l) % 133 = l := by omega
    unfold yD dgt
    rw [e1, e2, if_pos hr64, hdk]
    simp only [hdk]
  rw [hsum]
  have hiff : ∀ N : Nat, N % 5 = v ↔ ((N : Nat) : ZMod 5) = (v : ZMod 5) := fun N => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hv]
  rw [hiff, quad_cast]
  rfl

theorem dotSum_eq (T : Nat → Nat) (CM3 M MR L1 ONES G v lo : Nat) : ∀ n,
    dotSum T CM3 M MR L1 ONES G v lo n =
      ∑ i ∈ range n, dotLeaf T CM3 M MR L1 ONES G v (lo + i) (hnxC (lo + i))
  | 0 => rfl
  | n + 1 => by
    change CFSG.KC.Loop.strictN (dotSum T CM3 M MR L1 ONES G v lo n) (fun a => Nat.add a
      (dotLeaf T CM3 M MR L1 ONES G v (Nat.add lo n) (hnxC (Nat.add lo n)))) = _
    rw [strictN_eq', dotSum_eq T CM3 M MR L1 ONES G v lo n, Finset.sum_range_succ]
    rfl

theorem card_dot_eq {T : Nat → Nat} {CM3 M MS REP ONES L1 MR G v : Nat}
    (hc : constsOK CM3 M = true) (hm : masksOK MS = true)
    (hd : dotConstsOK MS REP ONES L1 MR = true) (hG : Canon 5 133 13 G) (hv : v < 5) :
    ((range 1140000).filter fun i =>
      xvec T i ⬝ᵥ (ordMat 5 133 13 1729 G *ᵥ xvec T i) = (v : ZMod 5)).card =
      ∑ b ∈ range 17813, dotLeaf T CM3 M MR L1 ONES G v b (hnxC b) := by
  rw [Finset.card_filter, ← sum_leaves]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotLeaf_eq hc hm hd hG hv (hnxC_le b), Finset.card_filter]

theorem ordMat_lane (Z : Nat) (i j : Fin 133) :
    ordMat 5 133 13 1729 Z i j = ((lane 13 Z (133 * i.val + j.val) : Nat) : ZMod 5) := by
  unfold ordMat lane
  have e : 13 * (133 * i.val + j.val) = 1729 * i.val + 13 * j.val := by ring
  rw [e]

theorem addHN_sound {X Y : Nat} (hX : Canon 5 133 13 X) (hY : Canon 5 133 13 Y) :
    Canon 5 133 13 (CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (X + Y)) ∧
      ordMat 5 133 13 1729 (CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (X + Y)) =
        ordMat 5 133 13 1729 X + ordMat 5 133 13 1729 Y := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, -, -⟩ := consts_facts CFSG.KD.OrdHN.consts
  have hXe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hX.1
  have hYe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hY.1
  have hb : ∀ t < 133 * 133, lane 13 X t + lane 13 Y t ≤ 8 := fun t ht => by
    have := hX.2 t ht
    have := hY.2 t ht
    omega
  have e : CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (X + Y) =
      pk 13 (133 * 133) (fun t => (lane 13 X t + lane 13 Y t) % 5) := by
    rw [hL, hH]
    conv_lhs => rw [hXe, hYe, pk_add]
    refine redP_pk (by norm_num) hT (fun t ht => ?_) (fun t ht => ?_)
    · have := hb t ht
      have h12 : (2 : Nat) ^ (13 - 1) = 4096 := by norm_num
      rw [h12]
      omega
    · have := hb t ht
      have h10 : (5 : Nat) * 2 ^ (9 + 1) = 5120 := by norm_num
      rw [h10]
      omega
  have hlt : ∀ t < 133 * 133, (lane 13 X t + lane 13 Y t) % 5 < 2 ^ 13 := fun t _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [e]
  refine ⟨canon_pk (fun t _ => Nat.mod_lt _ (by norm_num)) (by norm_num), ?_⟩
  funext i j
  have hs : 133 * i.val + j.val < 133 * 133 := by have := i.isLt; have := j.isLt; omega
  rw [Matrix.add_apply, ordMat_lane, ordMat_lane, ordMat_lane, lane_pk hlt hs, ZMod.natCast_mod,
    Nat.cast_add]

theorem dotSum_add (T : Nat → Nat) (CM3 M MR L1 ONES G v : Nat) {a n s : Nat}
    (h : dotSum T CM3 M MR L1 ONES G v a n = s) {u : Nat}
    (hu : ∑ b ∈ range a, dotLeaf T CM3 M MR L1 ONES G v b (hnxC b) = u) :
    ∑ b ∈ range (a + n), dotLeaf T CM3 M MR L1 ONES G v b (hnxC b) = u + s := by
  rw [Finset.sum_range_add, hu, ← h, dotSum_eq]

end CFSG.KS.SporSch.HNXP

end
