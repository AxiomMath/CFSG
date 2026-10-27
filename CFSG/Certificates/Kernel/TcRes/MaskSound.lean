module

public import CFSG.Certificates.Kernel.TcRes.MovedAnaSound
public import CFSG.Certificates.Kernel.TcRes.C2SweepSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK CFSG.KC.TcRes.Lane

section Lanes

def LaneW (w K x : ℕ) (f : ℕ → ℕ) (B : ℕ) : Prop := ∀ k < K, fld x w k = f k ∧ f k ≤ B

theorem LaneW.add {w K a b : ℕ} {f g : ℕ → ℕ} {A B : ℕ} (ha : LaneW w K a f A)
    (hb : LaneW w K b g B) (hAB : A + B < 2 ^ w) : LaneW w K (a + b) (fun k => f k + g k) (A + B) := by
  intro k hk
  refine ⟨?_, Nat.add_le_add (ha k hk).2 (hb k hk).2⟩
  change fld (a + b) w k = f k + g k
  rw [fld_add_low (fun k' hk' => ?_), (ha k hk).1, (hb k hk).1]
  rw [(ha k' (by omega)).1, (hb k' (by omega)).1]
  have h1 := (ha k' (by omega)).2
  have h2 := (hb k' (by omega)).2
  omega

theorem LaneW.smul {w K a : ℕ} {f : ℕ → ℕ} {A : ℕ} (c : ℕ) (ha : LaneW w K a f A)
    (hc : c * A < 2 ^ w) : LaneW w K (c * a) (fun k => c * f k) (c * A) := by
  intro k hk
  refine ⟨?_, Nat.mul_le_mul_left c (ha k hk).2⟩
  change fld (c * a) w k = c * f k
  rw [fld_smul_low (fun k' hk' => ?_), (ha k hk).1]
  rw [(ha k' (by omega)).1]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left c (ha k' (by omega)).2) hc

theorem LaneW.mono {w K a : ℕ} {f : ℕ → ℕ} {A B : ℕ} (ha : LaneW w K a f A) (h : A ≤ B) :
    LaneW w K a f B := fun k hk => ⟨(ha k hk).1, (ha k hk).2.trans h⟩

theorem LaneW.self {w K a B : ℕ} (h : ∀ k < K, fld a w k ≤ B) : LaneW w K a (fun k => fld a w k) B :=
  fun k hk => ⟨rfl, h k hk⟩

theorem testBit_lane {x w k : ℕ} (hw : 0 < w) (h : fld x w k ≤ 1) :
    x.testBit (w * k) = decide (fld x w k = 1) := by
  have e := testBit_fld x w k 0
  rw [add_zero, decide_eq_true hw, Bool.true_and] at e
  rw [← e]
  rcases (by omega : fld x w k = 0 ∨ fld x w k = 1) with h0 | h0 <;> rw [h0] <;> decide

end Lanes

section Squash

theorem squash_walk (x : ℕ) : ∀ n ≤ 72, ∀ i, (Nat.rec (motive := fun _ => ℕ) 0
    (fun g ih => strictN ih fun a => Nat.lor (Nat.shiftLeft a 1)
      (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 g) 5)) 1)) n).testBit i =
      (decide (i < n) && x.testBit (5 * (72 - n + i))) := by
  intro n
  induction n with
  | zero => intro _ i; simp
  | succ n ih =>
    intro hn i
    change (strictN (Nat.rec (motive := fun _ => ℕ) 0
      (fun g ih => strictN ih fun a => Nat.lor (Nat.shiftLeft a 1)
        (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 g) 5)) 1)) n) fun a =>
          Nat.lor (Nat.shiftLeft a 1) (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 n) 5)) 1)).testBit i = _
    rw [strictN_eq, nlor, nshl, nland, nshr, nmul, nsub, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    rcases i with _ | i
    · simp only [ge_iff_le, Nat.le_zero, one_ne_zero, decide_false, Bool.false_and,
        Nat.testBit_one_zero, Bool.and_true, Bool.false_or, Nat.zero_lt_succ, decide_true,
        Bool.true_and]
      congr 1
      omega
    · have h1 : (1 : ℕ).testBit (i + 1) = false := by
        rw [Nat.testBit_succ]
        simp
      simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le, decide_true, Bool.true_and,
        Nat.add_sub_cancel, h1, Bool.and_false, Bool.or_false]
      rw [ih (by omega) i]
      have e : 5 * (72 - n + i) = 5 * (72 - (n + 1) + (i + 1)) := by omega
      rw [e, decide_eq_decide.2 (by omega : i < n ↔ i + 1 < n + 1)]

theorem testBit_squash (x i : ℕ) : (squash x).testBit i = (decide (i < 72) && x.testBit (5 * i)) := by
  have h := squash_walk x 72 le_rfl i
  rw [Nat.sub_self, zero_add] at h
  exact h

theorem squash_lt (x : ℕ) : squash x < 2 ^ 72 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_squash]
    simp [show ¬ i < 72 by omega]

end Squash

section SquashEight

@[expose] def spread8 (b : ℕ) : ℕ :=
  Nat.add (Nat.mod b 2) (Nat.add (Nat.mul (Nat.mod (Nat.div b 2) 2) 256)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 4) 2) 65536)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 8) 2) 16777216)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 16) 2) 4294967296)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 32) 2) 1099511627776)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 64) 2) 281474976710656)
      (Nat.mul (Nat.mod (Nat.div b 128) 2) 72057594037927936)))))))

theorem gather8B : allLt 256 (fun b => allLt 8 fun k =>
    Nat.beq (Nat.mod (Nat.div (Nat.land (Nat.shiftRight (Nat.mul (spread8 b) 72624976668147840) 56)
      255) (Nat.pow 2 k)) 2) (Nat.mod (Nat.div (spread8 b) (Nat.pow 2 (Nat.mul 8 k))) 2)) = true := by
  decide +kernel

theorem spread8_eq : allLt 2 (fun f0 => allLt 2 fun f1 => allLt 2 fun f2 => allLt 2 fun f3 =>
    allLt 2 fun f4 => allLt 2 fun f5 => allLt 2 fun f6 => allLt 2 fun f7 =>
    Nat.beq (spread8 (Nat.add f0 (Nat.add (Nat.mul 2 f1) (Nat.add (Nat.mul 4 f2)
      (Nat.add (Nat.mul 8 f3) (Nat.add (Nat.mul 16 f4) (Nat.add (Nat.mul 32 f5)
      (Nat.add (Nat.mul 64 f6) (Nat.mul 128 f7)))))))))
    (Nat.add f0 (Nat.add (Nat.mul 256 f1) (Nat.add (Nat.mul 65536 f2)
      (Nat.add (Nat.mul 16777216 f3) (Nat.add (Nat.mul 4294967296 f4)
      (Nat.add (Nat.mul 1099511627776 f5) (Nat.add (Nat.mul 281474976710656 f6)
        (Nat.mul 72057594037927936 f7))))))))) = true := by
  decide +kernel

theorem gather8 {b k : ℕ} (hb : b < 256) (hk : k < 8) :
    (((spread8 b * 72624976668147840) >>> 56) &&& 255).testBit k =
      (spread8 b).testBit (8 * k) := by
  have h := Lane.allLt_iff.1 (Lane.allLt_iff.1 gather8B b hb) k hk
  rw [beq_eq_true] at h
  simp only [nmod, ndiv, nland, nshr, nmul, npow] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h]

theorem gather8_lt (y : ℕ) : ((y * 72624976668147840) >>> 56) &&& 255 < 2 ^ 8 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_gather8 {y : ℕ} (hy : y < 2 ^ 64) (hl : ∀ k < 8, fld y 8 k ≤ 1) {k : ℕ}
    (hk : k < 8) : (((y * 72624976668147840) >>> 56) &&& 255).testBit k = y.testBit (8 * k) := by
  have e := eq_sum_lanes 8 8 y hy
  norm_num [Finset.sum_range_succ] at e
  have l0 := hl 0 (by norm_num)
  have l1 := hl 1 (by norm_num)
  have l2 := hl 2 (by norm_num)
  have l3 := hl 3 (by norm_num)
  have l4 := hl 4 (by norm_num)
  have l5 := hl 5 (by norm_num)
  have l6 := hl 6 (by norm_num)
  have l7 := hl 7 (by norm_num)
  have hs := Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1
    (Lane.allLt_iff.1 (Lane.allLt_iff.1 spread8_eq _ (by omega : fld y 8 0 < 2)) _ (by omega : fld y 8 1 < 2))
    _ (by omega : fld y 8 2 < 2)) _ (by omega : fld y 8 3 < 2)) _ (by omega : fld y 8 4 < 2))
    _ (by omega : fld y 8 5 < 2)) _ (by omega : fld y 8 6 < 2)) _ (by omega : fld y 8 7 < 2)
  rw [beq_eq_true] at hs
  have h := gather8 (b := Nat.add (fld y 8 0) (Nat.add (Nat.mul 2 (fld y 8 1))
    (Nat.add (Nat.mul 4 (fld y 8 2)) (Nat.add (Nat.mul 8 (fld y 8 3))
    (Nat.add (Nat.mul 16 (fld y 8 4)) (Nat.add (Nat.mul 32 (fld y 8 5))
    (Nat.add (Nat.mul 64 (fld y 8 6)) (Nat.mul 128 (fld y 8 7)))))))))
    (by simp only [nadd, nmul]; omega) hk
  have hS : Nat.add (fld y 8 0) (Nat.add (Nat.mul 256 (fld y 8 1))
      (Nat.add (Nat.mul 65536 (fld y 8 2)) (Nat.add (Nat.mul 16777216 (fld y 8 3))
      (Nat.add (Nat.mul 4294967296 (fld y 8 4)) (Nat.add (Nat.mul 1099511627776 (fld y 8 5))
      (Nat.add (Nat.mul 281474976710656 (fld y 8 6))
        (Nat.mul 72057594037927936 (fld y 8 7)))))))) = y := by
    simp only [nadd, nmul]
    omega
  rw [hs, hS] at h
  exact h

theorem squash8_rec {x : ℕ} (hl : ∀ k < 240, fld x 8 k ≤ 1) : ∀ n ≤ 30, ∀ j,
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 i) 72624976668147840) 56) 255)
          (Nat.mul 8 i))) n).testBit j = (decide (j < 8 * n) && x.testBit (8 * j)) := by
  intro n
  induction n with
  | zero => intro _ j; simp
  | succ n ih =>
    intro hn j
    change (strictN (Nat.rec (motive := fun _ => ℕ) 0
      (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 i) 72624976668147840) 56) 255)
          (Nat.mul 8 i))) n) fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 n) 72624976668147840) 56) 255)
          (Nat.mul 8 n))).testBit j = _
    rw [strictN_eq, nlor, Nat.testBit_or, ih (by omega) j]
    simp only [nshl, nmul, nland, nshr]
    rw [Nat.testBit_shiftLeft]
    have hy : fld x 64 n < 2 ^ 64 := fld_lt _ _ _
    have hyl : ∀ k < 8, fld (fld x 64 n) 8 k ≤ 1 := fun k hk => by
      have e := Lane.fld_fld x 8 8 n k hk
      rw [show (8 * 8 : ℕ) = 64 from rfl] at e
      rw [e]
      exact hl _ (by omega)
    by_cases h1 : j < 8 * n
    · have : ¬ 8 * n ≤ j := by omega
      simp [h1, this, show j < 8 * (n + 1) by omega]
    · by_cases h2 : j < 8 * (n + 1)
      · have hk : j - 8 * n < 8 := by omega
        have hg := testBit_gather8 hy hyl hk
        have e2 := testBit_fld x 64 n (8 * (j - 8 * n))
        rw [decide_eq_true (by omega : 8 * (j - 8 * n) < 64), Bool.true_and] at e2
        have e3 : 64 * n + 8 * (j - 8 * n) = 8 * j := by omega
        rw [e3] at e2
        simp only [h1, decide_false, Bool.false_and, Bool.false_or, ge_iff_le,
          show 8 * n ≤ j by omega, decide_true, Bool.true_and]
        rw [hg, e2, decide_eq_true h2, Bool.true_and]
      · have hb : (((fld x 64 n * 72624976668147840) >>> 56) &&& 255).testBit (j - 8 * n) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (gather8_lt _)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, hb]

theorem testBit_squash8 {x : ℕ} (hl : ∀ k < 240, fld x 8 k ≤ 1) (j : ℕ) :
    (squash8 x).testBit j = (decide (j < 240) && x.testBit (8 * j)) :=
  squash8_rec hl 30 le_rfl j

theorem squash8_lt {x : ℕ} (hl : ∀ k < 240, fld x 8 k ≤ 1) : squash8 x < 2 ^ 240 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_squash8 hl]
    simp [show ¬ i < 240 by omega]

end SquashEight

section ZlFive

theorem fld_shr_land {w K y s t c k : ℕ} (hw : 1 ≤ w) (hst : s + t ≤ w) (hc : c = 2 ^ t - 1)
    (hk : k < K) : fld ((y >>> s) &&& (c * lowW w K)) w k = fld y w k / 2 ^ s % 2 ^ t := by
  have hct : c < 2 ^ w := by
    rw [hc]
    have : 2 ^ t ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ t := Nat.two_pow_pos t
    omega
  rw [fld_land, fld_mul_low hw hct hk, hc, Nat.and_two_pow_sub_one_eq_mod, fld_eq, fld_eq,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, mul_comm (2 ^ s),
    ← Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : t ≤ w))]
  have e : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : t ≤ w - s))]

theorem fld_zl5 {x k : ℕ} (hxl : ∀ k < 240, fld x 8 k ≤ 128) (hk : k < 240) :
    fld (zl5 x) 8 k = if fld x 8 k % 5 = 0 then 1 else 0 := by
  have hw : (1 : ℕ) ≤ 8 := by norm_num
  have hL : LOW8 = lowW 8 240 := rfl
  have hLt : ∀ c, c < 256 → c * lowW 8 240 < 2 ^ (8 * 240) := fun c hc =>
    mul_low_lt hw (lt_of_lt_of_eq hc (by norm_num))
  have hS : ∀ y, ∀ k < 240, fld (Nat.add (Nat.land y (Nat.mul LOW8 15))
      (Nat.land (Nat.shiftRight y 4) (Nat.mul LOW8 15))) 8 k = fld y 8 k % 16 + fld y 8 k / 16 ∧
      Nat.add (Nat.land y (Nat.mul LOW8 15)) (Nat.land (Nat.shiftRight y 4) (Nat.mul LOW8 15)) <
        2 ^ (8 * 240) := by
    intro y k hk
    have e1 : ∀ k < 240, fld (Nat.land y (Nat.mul LOW8 15)) 8 k = fld y 8 k % 16 := fun k hk => by
      rw [nland, nmul, hL, mul_comm, fld_land, fld_mul_low hw (by norm_num) hk]
      exact Nat.and_two_pow_sub_one_eq_mod _ 4
    have e2 : ∀ k < 240, fld (Nat.land (Nat.shiftRight y 4) (Nat.mul LOW8 15)) 8 k =
        fld y 8 k / 16 := fun k hk => by
      rw [nland, nshr, nmul, hL, mul_comm, fld_shr_land (t := 4) hw (by norm_num) (by norm_num) hk]
      have := fld_lt y 8 k
      norm_num at this ⊢
      omega
    have b1 : Nat.land y (Nat.mul LOW8 15) < 2 ^ (8 * 240) :=
      lt_of_le_of_lt Nat.and_le_right (by rw [nmul, hL, mul_comm]; exact hLt 15 (by norm_num))
    have b2 : Nat.land (Nat.shiftRight y 4) (Nat.mul LOW8 15) < 2 ^ (8 * 240) :=
      lt_of_le_of_lt Nat.and_le_right (by rw [nmul, hL, mul_comm]; exact hLt 15 (by norm_num))
    have hc : ∀ k < 240, fld (Nat.land y (Nat.mul LOW8 15)) 8 k +
        fld (Nat.land (Nat.shiftRight y 4) (Nat.mul LOW8 15)) 8 k < 2 ^ 8 := fun k hk => by
      rw [e1 k hk, e2 k hk]
      have := fld_lt y 8 k
      norm_num at this ⊢
      omega
    obtain ⟨h1, h2⟩ := fld_add_w b1 b2 hc hk
    exact ⟨by rw [nadd, h1, e1 k hk, e2 k hk], h2⟩
  set x1 := Nat.add (Nat.land x (Nat.mul LOW8 15)) (Nat.land (Nat.shiftRight x 4) (Nat.mul LOW8 15))
    with hx1
  set y1 := Nat.add (Nat.land x1 (Nat.mul LOW8 15)) (Nat.land (Nat.shiftRight x1 4) (Nat.mul LOW8 15))
    with hy1
  have hy1l : ∀ k < 240, fld y1 8 k = (fld x 8 k % 16 + fld x 8 k / 16) % 16 +
      (fld x 8 k % 16 + fld x 8 k / 16) / 16 := fun k hk => by
    rw [(hS x1 k hk).1, (hS x k hk).1]
  have h16 : 16 * lowW 8 240 < 2 ^ (8 * 240) := hLt 16 (by norm_num)
  have hzc : ∀ k < 240, fld y1 8 k + fld (16 * lowW 8 240) 8 k < 2 ^ 8 := fun k hk => by
    rw [hy1l k hk, fld_mul_low hw (by norm_num) hk]
    have := hxl k hk
    norm_num
    omega
  set z := Nat.add y1 (Nat.mul LOW8 16) with hz
  have hzl : ∀ k < 240, fld z 8 k = fld y1 8 k + 16 := fun k hk => by
    rw [hz, nadd, nmul, hL, mul_comm, (fld_add_w (hS x1 0 (by norm_num)).2 h16 hzc hk).1,
      fld_mul_low hw (by norm_num) hk]
  have hzb : z < 2 ^ (8 * 240) := by
    rw [hz, nadd, nmul, hL, mul_comm]
    exact (fld_add_w (hS x1 0 (by norm_num)).2 h16 hzc (by norm_num : 0 < 240)).2
  have hE : ∀ c, c ≤ 15 → fld (((z - LOW8 * c) >>> 4) &&& LOW8) 8 k =
      (fld z 8 k - c) / 16 % 2 := by
    intro c hc
    have e := fld_shr_land (K := 240) (y := z - c * lowW 8 240) (s := 4) (t := 1) (c := 1) hw
      (by norm_num) (by norm_num) hk
    rw [one_mul] at e
    rw [hL, mul_comm (lowW 8 240) c, e, (fld_sub_low hw hzb (by omega : c < 2 ^ 8) (fun k hk => by
      rw [hzl k hk]
      omega) hk).1]
    norm_num
  have hE1 : fld (((z - LOW8) >>> 4) &&& LOW8) 8 k = (fld z 8 k - 1) / 16 % 2 := by
    have := hE 1 (by norm_num)
    rwa [mul_one] at this
  have hLk : fld LOW8 8 k = 1 := by
    have := fld_mul_low (K := 240) hw (by norm_num : (1 : ℕ) < 2 ^ 8) hk
    rwa [one_mul] at this
  simp only [zl5, strictN_eq]
  rw [← hx1, ← hy1, ← hz]
  simp only [nlor, nxor, nland, nshr, nsub, nmul]
  rw [fld_lor, fld_xor, hE1, fld_lor, fld_land, hE 5 (by norm_num), fld_xor, hE 6 (by norm_num),
    fld_lor, hE 15 (by norm_num), fld_land, hE 10 (by norm_num), fld_xor, hE 11 (by norm_num), hLk,
    hzl k hk, hy1l k hk]
  have := hxl k hk
  generalize fld x 8 k = a at this ⊢
  interval_cases a <;> decide

end ZlFive

section MasksSix

theorem dot5_lanes {RC : ℕ → ℕ} (hRC : ∀ m < 6, ∀ g < 72, fld (RC m) 5 g ≤ 2) (u : ℕ) :
    LaneW 5 72 (dot5 RC u) (fun g => dg u 0 * fld (RC 0) 5 g + (dg u 1 * fld (RC 1) 5 g +
      (dg u 2 * fld (RC 2) 5 g + (dg u 3 * fld (RC 3) 5 g + (dg u 4 * fld (RC 4) 5 g +
      dg u 5 * fld (RC 5) 5 g))))) 24 := by
  have hR : ∀ m < 6, LaneW 5 72 (RC m) (fun g => fld (RC m) 5 g) 2 := fun m hm =>
    LaneW.self (hRC m hm)
  have hd : ∀ m, dg u m ≤ 2 := fun m => by have := dg_lt u m; omega
  have hs : ∀ m < 6, LaneW 5 72 (dg u m * RC m) (fun g => dg u m * fld (RC m) 5 g) 4 := fun m hm =>
    ((hR m hm).smul (dg u m) (by have := hd m; norm_num; omega)).mono
      (by have := hd m; nlinarith)
  exact ((hs 0 (by norm_num)).add ((hs 1 (by norm_num)).add ((hs 2 (by norm_num)).add
    ((hs 3 (by norm_num)).add ((hs 4 (by norm_num)).add (hs 5 (by norm_num)) (by norm_num))
    (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))

theorem rc_cast {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) {g : ℕ} (hg : g < 72)
    (m : Fin 6) : ((fld (RC m) 5 g : ℕ) : ZMod 3) = ((vecOf 6 V g m : ℤ) : ZMod 3) := by
  have h9 : (9 : ZMod 3) = 0 := by decide
  rw [rc_lane hrc hg m.2, ZMod.natCast_mod]
  simp only [vecOf, show (16 * 6 : ℕ) = 96 from rfl]
  push_cast
  linear_combination h9

theorem mset_kv {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) (x : ℕ) :
    mset 72 (kv RC x) = {g | g < 72 ∧ ∑ m : Fin 6, v3 x m * ((vecOf 6 V g m : ℤ) : ZMod 3) = 0} := by
  have hD := dot5_lanes (fun m hm g hg => rc_le hrc hg hm) x
  ext g
  simp only [mset, Set.mem_setOf_eq]
  refine and_congr_right fun hg => ?_
  have hz : fld (zl LOW5 (dot5 RC x)) 5 g = if fld (dot5 RC x) 5 g % 3 = 0 then 1 else 0 :=
    fld_zl_any (w := 5) (K := 72) le_rfl (fun k hk => by
      rw [(hD k hk).1]
      exact le_trans (hD k hk).2 (by norm_num)) hg
  have hle : fld (zl LOW5 (dot5 RC x)) 5 g ≤ 1 := by rw [hz]; split_ifs <;> norm_num
  change bit (squash (zl LOW5 (dot5 RC x))) g = true ↔ _
  rw [bit_iff, testBit_squash, decide_eq_true hg, Bool.true_and,
    testBit_lane (by norm_num) hle, hz, (hD g hg).1, decide_eq_true_iff]
  rw [Fin.sum_univ_six]
  simp only [v3, ← rc_cast hrc hg]
  have v0 : ((0 : Fin 6) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 6) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 6) : ℕ) = 2 := rfl
  have v3' : ((3 : Fin 6) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have v5' : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [v0, v1, v2, v3', v4, v5']
  norm_cast
  rw [natCast_zmod3_eq_zero]
  simp only [add_assoc]
  split_ifs with h <;> simp [h]

theorem kv_lt (RC : ℕ → ℕ) (x : ℕ) : kv RC x < 2 ^ 72 := squash_lt _

theorem mset_kmask {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) (u1 u2 : ℕ) :
    mset 72 (kmask RC u1 u2) = PhiP (vecOf 6 V) (v3 u1) (v3 u2) := by
  have e : ∀ g, bit (kmask RC u1 u2) g = (bit (kv RC u1) g && bit (kv RC u2) g) := fun g => by
    have h1 : ∀ m i, bit m i = m.testBit i := fun m i => by
      cases h : m.testBit i
      · cases h' : bit m i
        · rfl
        · exact absurd (bit_iff.1 h') (by rw [h]; decide)
      · exact bit_iff.2 h
    rw [h1, h1, h1]
    rw [kmask, strictN_eq, strictN_eq, nland, Nat.testBit_and]
    rfl
  have h1 := mset_kv hrc u1
  have h2 := mset_kv hrc u2
  ext g
  have m1 := congrArg (g ∈ ·) h1
  have m2 := congrArg (g ∈ ·) h2
  simp only [mset, Set.mem_setOf_eq, eq_iff_iff] at m1 m2
  simp only [mset, PhiP, Set.mem_setOf_eq, e, Bool.and_eq_true]
  constructor
  · rintro ⟨hg, ha, hb⟩
    exact ⟨hg, (m1.1 ⟨hg, ha⟩).2, (m2.1 ⟨hg, hb⟩).2⟩
  · rintro ⟨hg, ha, hb⟩
    exact ⟨hg, (m1.2 ⟨hg, ha⟩).2, (m2.2 ⟨hg, hb⟩).2⟩

theorem kmask_lt (RC : ℕ → ℕ) (u1 u2 : ℕ) : kmask RC u1 u2 < 2 ^ 72 := by
  rw [kmask, strictN_eq, strictN_eq]
  exact lt_of_le_of_lt Nat.and_le_left (kv_lt RC u1)

theorem sub_mem_kv {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) (x : ℕ) :
    ∀ a ∈ mset 72 (kv RC x), ∀ b ∈ mset 72 (kv RC x), ∀ d < 72,
      vecOf 6 V d = vecOf 6 V a - vecOf 6 V b → d ∈ mset 72 (kv RC x) := by
  rw [mset_kv hrc]
  rintro a ⟨-, ha⟩ b ⟨-, hb⟩ d hd e
  refine ⟨hd, ?_⟩
  simp only [e, Pi.sub_apply, Int.cast_sub, mul_sub]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ha hb ⊢
  linear_combination ha - hb

theorem sub_mem_kmask {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) (u1 u2 : ℕ) :
    ∀ a ∈ mset 72 (kmask RC u1 u2), ∀ b ∈ mset 72 (kmask RC u1 u2), ∀ d < 72,
      vecOf 6 V d = vecOf 6 V a - vecOf 6 V b → d ∈ mset 72 (kmask RC u1 u2) := by
  rw [mset_kmask hrc]
  rintro a ⟨-, ha1, ha2⟩ b ⟨-, hb1, hb2⟩ d hd e
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ha1 hb1 ha2 hb2
  refine ⟨hd, ?_, ?_⟩ <;> simp only [e, Pi.sub_apply, Int.cast_sub, mul_sub, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  · linear_combination ha1 - hb1
  · linear_combination ha2 - hb2

end MasksSix

section MasksEight

theorem rc5_lane {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) {g : ℕ}
    (hg : g < 240) {m : ℕ} (hm : m < 8) : fld (RC m) 8 g = (fld (fld V 128 g) 16 m + 3) % 5 := by
  have h := hrc g hg
  simp only [rc5OK, strictB_eq, allLt_iff, beq_eq_true, nadd, nmod] at h
  exact h m hm

theorem rc5_le {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) {g : ℕ}
    (hg : g < 240) {m : ℕ} (hm : m < 8) : fld (RC m) 8 g ≤ 4 := by
  rw [rc5_lane hrc hg hm]
  have := Nat.mod_lt (fld (fld V 128 g) 16 m + 3) (by norm_num : 0 < 5)
  omega

theorem um_le (B c m : ℕ) : um B c m ≤ 4 := by
  have := Nat.mod_lt (sumLt 4 fun i => Nat.mul (dg5 c i) (dg5 (fld B 20 i) m)) (by norm_num : 0 < 5)
  change _ % 5 ≤ 4
  omega

theorem dot8_lanes_aux {RC : ℕ → ℕ} (hR : ∀ m < 8, ∀ g < 240, fld (RC m) 8 g ≤ 4) (B c : ℕ) :
    ∀ n ≤ 8, LaneW 8 240 (∑ m ∈ Finset.range n, um B c m * RC m)
      (fun g => ∑ m ∈ Finset.range n, um B c m * fld (RC m) 8 g) (16 * n) := by
  intro n
  induction n with
  | zero => intro _ k _; simp [fld_zero]
  | succ n ih =>
    intro hn
    have hs : LaneW 8 240 (um B c n * RC n) (fun g => um B c n * fld (RC n) 8 g) 16 :=
      ((LaneW.self (hR n (by omega))).smul (um B c n) (by have := um_le B c n; norm_num; omega)).mono
        (by have := um_le B c n; omega)
    have h := (ih (by omega)).add hs (by norm_num; omega)
    intro k hk
    obtain ⟨h1, h2⟩ := h k hk
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_range_succ]
      exact h1
    · simp only [Finset.sum_range_succ]
      simp only at h2
      omega

theorem dot8_lanes {RC : ℕ → ℕ} (hR : ∀ m < 8, ∀ g < 240, fld (RC m) 8 g ≤ 4) (B c : ℕ) :
    LaneW 8 240 (dot8 RC B c) (fun g => ∑ m ∈ Finset.range 8, um B c m * fld (RC m) 8 g) 128 := by
  have h := dot8_lanes_aux hR B c 8 le_rfl
  have e : dot8 RC B c = ∑ m ∈ Finset.range 8, um B c m * RC m := by
    rw [dot8, sumLt_eq]
    rfl
  rw [e]
  exact h

theorem natCast_zmod5_eq_zero (n : ℕ) : (n : ZMod 5) = 0 ↔ n % 5 = 0 := by
  rw [← ZMod.natCast_mod]
  have := Nat.mod_lt n (by norm_num : 0 < 5)
  generalize n % 5 = a at this ⊢
  interval_cases a <;> decide

theorem rc5_cast {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) {g : ℕ}
    (hg : g < 240) (m : Fin 8) : ((fld (RC m) 8 g : ℕ) : ZMod 5) = ((vecOf 8 V g m : ℤ) : ZMod 5) := by
  have h10 : (10 : ZMod 5) = 0 := by decide
  rw [rc5_lane hrc hg m.2, ZMod.natCast_mod]
  simp only [vecOf, show (16 * 8 : ℕ) = 128 from rfl]
  push_cast
  linear_combination h10

theorem um_cast (B c : ℕ) (m : Fin 8) : ((um B c m : ℕ) : ZMod 5) = lam B (v5 c) m := by
  change (((sumLt 4 fun i => Nat.mul (dg5 c i) (dg5 (fld B 20 i) m)) % 5 : ℕ) : ZMod 5) = _
  rw [ZMod.natCast_mod, sumLt_eq]
  simp only [lam, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v5, bvec, nmul, Nat.cast_sum,
    Nat.cast_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ((dg5 c i : ℕ) : ZMod 5) * ((dg5 (fld B 20 i) m : ℕ) : ZMod 5)) 4]

theorem mset_kv8 {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) (B c : ℕ) :
    mset 240 (kv8 RC B c) =
      {g | g < 240 ∧ ∑ m : Fin 8, lam B (v5 c) m * ((vecOf 8 V g m : ℤ) : ZMod 5) = 0} := by
  have hD := dot8_lanes (fun m hm g hg => rc5_le hrc hg hm) B c
  have hz : ∀ k < 240, fld (zl5 (dot8 RC B c)) 8 k =
      if fld (dot8 RC B c) 8 k % 5 = 0 then 1 else 0 := fun k hk =>
    fld_zl5 (fun k hk => by rw [(hD k hk).1]; exact (hD k hk).2) hk
  have hl : ∀ k < 240, fld (zl5 (dot8 RC B c)) 8 k ≤ 1 := fun k hk => by
    rw [hz k hk]
    split_ifs <;> norm_num
  ext g
  simp only [mset, Set.mem_setOf_eq]
  refine and_congr_right fun hg => ?_
  change bit (squash8 (zl5 (dot8 RC B c))) g = true ↔ _
  rw [bit_iff, testBit_squash8 hl, decide_eq_true hg, Bool.true_and,
    testBit_lane (by norm_num) (hl g hg), hz g hg, (hD g hg).1, decide_eq_true_iff]
  have key : ∀ m : Fin 8, lam B (v5 c) m * ((vecOf 8 V g m : ℤ) : ZMod 5) =
      ((um B c m * fld (RC m) 8 g : ℕ) : ZMod 5) := fun m => by
    rw [Nat.cast_mul, um_cast, rc5_cast hrc hg]
  rw [Finset.sum_congr rfl (fun m _ => key m), ← Nat.cast_sum,
    Fin.sum_univ_eq_sum_range (fun m => um B c m * fld (RC m) 8 g) 8, natCast_zmod5_eq_zero]
  split_ifs with h <;> simp [h]

theorem mset_kmask5 {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) (B c1 c2 : ℕ) :
    mset 240 (kmask5 RC B c1 c2) = PhiP5 (vecOf 8 V) (lam B (v5 c1)) (lam B (v5 c2)) := by
  have h1 : ∀ m i, bit m i = m.testBit i := fun m i => by
    cases h : m.testBit i
    · cases h' : bit m i
      · rfl
      · exact absurd (bit_iff.1 h') (by rw [h]; decide)
    · exact bit_iff.2 h
  have e : ∀ g, bit (kmask5 RC B c1 c2) g = (bit (kv8 RC B c1) g && bit (kv8 RC B c2) g) :=
    fun g => by
      rw [h1, h1, h1, kmask5, strictN_eq, strictN_eq, nland, Nat.testBit_and]
      rfl
  have m1 := mset_kv8 hrc B c1
  have m2 := mset_kv8 hrc B c2
  ext g
  have n1 := congrArg (g ∈ ·) m1
  have n2 := congrArg (g ∈ ·) m2
  simp only [mset, Set.mem_setOf_eq, eq_iff_iff] at n1 n2
  simp only [mset, PhiP5, Set.mem_setOf_eq, e, Bool.and_eq_true]
  constructor
  · rintro ⟨hg, ha, hb⟩
    exact ⟨hg, (n1.1 ⟨hg, ha⟩).2, (n2.1 ⟨hg, hb⟩).2⟩
  · rintro ⟨hg, ha, hb⟩
    exact ⟨hg, (n1.2 ⟨hg, ha⟩).2, (n2.2 ⟨hg, hb⟩).2⟩

theorem kmask5_lt {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) (B c1 c2 : ℕ) :
    kmask5 RC B c1 c2 < 2 ^ 240 := by
  have hD := dot8_lanes (fun m hm g hg => rc5_le hrc hg hm) B c1
  have hl : ∀ k < 240, fld (zl5 (dot8 RC B c1)) 8 k ≤ 1 := fun k hk => by
    rw [fld_zl5 (fun k hk => by rw [(hD k hk).1]; exact (hD k hk).2) hk]
    split_ifs <;> norm_num
  rw [kmask5, strictN_eq, strictN_eq]
  exact lt_of_le_of_lt Nat.and_le_left (squash8_lt hl)

theorem sub_mem_kv8 {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true) (B c : ℕ) :
    ∀ a ∈ mset 240 (kv8 RC B c), ∀ b ∈ mset 240 (kv8 RC B c), ∀ d < 240,
      vecOf 8 V d = vecOf 8 V a - vecOf 8 V b → d ∈ mset 240 (kv8 RC B c) := by
  rw [mset_kv8 hrc]
  rintro a ⟨-, ha⟩ b ⟨-, hb⟩ d hd e
  refine ⟨hd, ?_⟩
  simp only [e, Pi.sub_apply, Int.cast_sub, mul_sub]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ha hb ⊢
  linear_combination ha - hb

theorem sub_mem_kmask5 {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 240, rc5OK RC V g = true)
    (B c1 c2 : ℕ) : ∀ a ∈ mset 240 (kmask5 RC B c1 c2), ∀ b ∈ mset 240 (kmask5 RC B c1 c2),
      ∀ d < 240, vecOf 8 V d = vecOf 8 V a - vecOf 8 V b → d ∈ mset 240 (kmask5 RC B c1 c2) := by
  rw [mset_kmask5 hrc]
  rintro a ⟨-, ha1, ha2⟩ b ⟨-, hb1, hb2⟩ d hd e
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ha1 hb1 ha2 hb2
  refine ⟨hd, ?_, ?_⟩ <;> simp only [e, Pi.sub_apply, Int.cast_sub, mul_sub, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  · linear_combination ha1 - hb1
  · linear_combination ha2 - hb2

end MasksEight

section Perm

theorem pw_aux {τ : Tag} {N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool}
    {neg : ℕ → ℕ} (hD : DatumRaw τ N vec rt adj neg) (ψ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hlin : ∀ (x y : Fin τ.rank → ℤ) (n : ℤ), ψ (x - n • y) = ψ x - n • ψ y)
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y) {pw pa le : ℕ → ℕ}
    (hpar : ∀ g < N, τ.rank ≤ g → pa g < g ∧ le g < τ.rank ∧ rt (le g) (pa g) = g)
    (hs : ∀ g < τ.rank, pw g < N ∧ vec (pw g) = ψ (vec g))
    (hst : ∀ g < N, τ.rank ≤ g → pw (pa g) < N → pw g = rt (pw (le g)) (pw (pa g))) :
    ∀ g < N, pw g < N ∧ vec (pw g) = ψ (vec g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    by_cases hr : g < τ.rank
    · exact hs g hr
    · obtain ⟨hp, hl, hrt⟩ := hpar g hg (by omega)
      have h1 := ih _ hp (by omega)
      have h2 := hs _ hl
      rw [hst g hg (by omega) h1.1]
      obtain ⟨hlt, hv⟩ := hD.refl _ h2.1 _ h1.1
      refine ⟨hlt, ?_⟩
      have hl' := hD.refl _ (lt_of_lt_of_le hl hD.rank_le) _ (by omega : pa g < N)
      rw [hv, h1.2, h2.2, hiso, ← hlin, ← hl'.2, hrt]

theorem par_spec {n N W : ℕ} {yc rtR : ℕ → ℕ} {V X Y NEG PAR : ℕ} (hn1 : 1 ≤ n)
    (hroot : ∀ i < N, rootOK n N W yc rtR V X Y NEG PAR i = true) {i : ℕ} (hi : i < N)
    (hni : n ≤ i) : fld PAR 16 i &&& 255 < i ∧ fld PAR 16 i >>> 8 < n ∧
      fld (rtR (fld PAR 16 i >>> 8)) W (fld PAR 16 i &&& 255) = i := by
  have h := (root_lanes hn1 (hroot i hi)).2.2.2.2.2.2.2 hni
  simp only [parOK, strictB_eq, andB_eq_true, blt_eq_true, beq_eq_true, nland, nshr] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem pw_spec
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {adj : ℕ → ℕ → Bool} {yc : ℕ → ℕ}
    {V X Y NEG PAR RT REPS PW : ℕ}
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj (fun i => fld NEG 7 i))
    (hroot : ∀ i < 72, rootOK 6 72 7 yc (fun g => fld RT 504 g) V X Y NEG PAR i = true)
    {k : ℕ} (hpw : pwOK RT REPS PAR PW k = true) {w : WeylGroup Tag.E6}
    (hw : TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (k * 42)) M42) w) :
    ∀ g < 72, fld (fld PW 504 k) 7 g < 72 ∧ vec (fld (fld PW 504 k) 7 g) = w • vec g := by
  have h6 : Tag.E6.rank = 6 := rfl
  simp only [pwOK, strictB_eq, allLt_iff, nmul] at hpw
  set t := Nat.land (Nat.shiftRight REPS (k * 42)) M42 with ht
  set pw := fld PW 504 k with hpwd
  have hc : ∀ g < 72, (g < 6 → fld pw 7 g = tf t g) ∧
      (6 ≤ g → fld pw 7 g = rtv RT (tf t (fld PAR 16 g >>> 8)) (fld pw 7 (fld PAR 16 g &&& 255))) := by
    intro g hg
    have h := hpw g hg
    rw [boolRec_true] at h
    simp only [strictB_eq, beq_eq_true, blt_eq_true, nshr, nland] at h
    refine ⟨fun h1 => h.1 h1, fun h1 => h.2 ?_⟩
    cases hb : Nat.blt g 6
    · rfl
    · exact absurd (blt_eq_true.1 hb) (by omega)
  refine pw_aux hD (fun x => w • x) (fun x y n => by rw [smul_sub, smul_comm])
    (fun x y => iform_smul w x y) (pw := fun g => fld pw 7 g)
    (pa := fun g => fld PAR 16 g &&& 255) (le := fun g => fld PAR 16 g >>> 8) ?_ ?_ ?_
  · intro g hg hr
    exact par_spec (n := 6) (by norm_num) hroot hg (by rw [h6] at hr; exact hr)
  · intro g hg
    rw [h6] at hg
    rw [(hc g (by omega)).1 hg]
    obtain ⟨h1, h2⟩ := hw ⟨g, by rw [h6]; exact hg⟩
    refine ⟨h1, ?_⟩
    rw [h2, hD.simple ⟨g, by rw [h6]; exact hg⟩]
  · intro g hg hr hlt
    rw [h6] at hr
    have hl := (par_spec (n := 6) (by norm_num) hroot hg hr).2.1
    rw [(hc g hg).2 hr, ← (hc _ (by omega)).1 hl, rtv_eq_fld _ _ _ hlt]

theorem phq_spec
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {adj : ℕ → ℕ → Bool} {yc : ℕ → ℕ}
    {V X Y NEG PAR RT REPS PW : ℕ}
    (hD : DatumRaw Tag.E6 72 vec (fun g v => fld (fld RT 504 g) 7 v) adj (fun i => fld NEG 7 i))
    (hroot : ∀ i < 72, rootOK 6 72 7 yc (fun g => fld RT 504 g) V X Y NEG PAR i = true)
    (hpw : ∀ k < 25, pwOK RT REPS PAR PW k = true) {q : ℕ} (hq : q < 75) {w : WeylGroup Tag.E6}
    (hw : TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (q / 3 * 42)) M42) w) :
    ∀ g < 72, phq PW NEG q g < 72 ∧
      vec (phq PW NEG q g) = if q % 3 = 0 then w • vec g else -(w • vec g) := by
  intro g hg
  obtain ⟨h1, h2⟩ := pw_spec hD hroot (hpw (q / 3) (by omega)) hw g hg
  rw [phq, strictN_eq, boolRec_nat]
  simp only [nmod, ndiv]
  by_cases h0 : q % 3 = 0
  · rw [if_pos (beq_eq_true.2 h0), if_pos h0]
    exact ⟨h1, h2⟩
  · rw [if_neg (by rw [beq_eq_true]; exact h0), if_neg h0]
    obtain ⟨n1, n2⟩ := hD.neg _ h1
    exact ⟨n1, by rw [n2, h2]⟩

theorem pw8_spec {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    {yc RTs : ℕ → ℕ} {V X Y NEG PAR T0 PW : ℕ}
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)
    (hroot : ∀ i < 240, rootOK 8 240 8 yc RTs V X Y NEG PAR i = true)
    (hpw : pw8OK RTs T0 PAR PW = true) (ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ))
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y)
    (hψ : ∀ m : Fin Tag.E8.rank, ψ (vec m) = vec (fld T0 8 m)) (hT : ∀ m < 8, fld T0 8 m < 240) :
    ∀ g < 240, fld PW 8 g < 240 ∧ vec (fld PW 8 g) = ψ (vec g) := by
  have h8 : Tag.E8.rank = 8 := rfl
  simp only [pw8OK, allLt_iff] at hpw
  have hc : ∀ g < 240, (g < 8 → fld PW 8 g = fld T0 8 g) ∧
      (8 ≤ g → fld PW 8 g = fld (RTs (fld T0 8 (fld PAR 16 g >>> 8))) 8
        (fld PW 8 (fld PAR 16 g &&& 255))) := by
    intro g hg
    have h := hpw g hg
    rw [boolRec_true] at h
    simp only [strictB_eq, beq_eq_true, blt_eq_true, nshr, nland] at h
    refine ⟨fun h1 => h.1 h1, fun h1 => h.2 ?_⟩
    cases hb : Nat.blt g 8
    · rfl
    · exact absurd (blt_eq_true.1 hb) (by omega)
  refine pw_aux hD ψ (fun x y n => by rw [map_sub, map_zsmul]) hiso (pw := fun g => fld PW 8 g)
    (pa := fun g => fld PAR 16 g &&& 255) (le := fun g => fld PAR 16 g >>> 8) ?_ ?_ ?_
  · intro g hg hr
    exact par_spec (n := 8) (by norm_num) hroot hg (by rw [h8] at hr; exact hr)
  · intro g hg
    rw [h8] at hg
    rw [(hc g (by omega)).1 hg]
    exact ⟨hT g hg, (hψ ⟨g, by rw [h8]; exact hg⟩).symm⟩
  · intro g hg hr _
    rw [h8] at hr
    have hl := (par_spec (n := 8) (by norm_num) hroot hg hr).2.1
    rw [(hc g hg).2 hr, ← (hc _ (by omega)).1 hl]

end Perm

section Walk8

variable {vec : ℕ → Fin Tag.E8.rank → ℤ} {S : Set ℕ} {ph : ℕ → ℕ}

@[expose] def Conn8 (vec : ℕ → Fin Tag.E8.rank → ℤ) (S : Set ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen fun a b => a ∈ S ∧ b ∈ S ∧ iform (vec a) (vec b) ≠ 0

def Good8 (vec : ℕ → Fin Tag.E8.rank → ℤ) (S : Set ℕ) (ph : ℕ → ℕ) (x : ℕ) : Prop :=
  ∃ r ∈ S, Conn8 vec S r x ∧ Conn8 vec S r (ph r)

def WInv8 (vec : ℕ → Fin Tag.E8.rank → ℤ) (S : Set ℕ) (ph : ℕ → ℕ) (acc C rt : ℕ) : Prop :=
  (∀ x, acc.testBit x = true → x ∈ S ∧ (C.testBit x = true ∨ Good8 vec S ph x)) ∧
  (C ≠ 0 → rt ∈ S ∧ ∀ x, C.testBit x = true → acc.testBit x = true ∧ Conn8 vec S rt x)

theorem finOK_close8 {P C rt NB : ℕ} (h : finOK ph P 0 C rt NB = true) {acc : ℕ}
    (hI : WInv8 vec S ph acc C rt) : ∀ x, C.testBit x = true → Good8 vec S ph x := by
  intro x hx
  have hC : C ≠ 0 := fun h0 => by
    rw [h0, Nat.zero_testBit] at hx
    exact absurd hx (by decide)
  simp only [finOK, Lane.orB_eq_true, Lane.beq_eq_true, Lane.strictB_eq, Lane.andB_eq_true,
    Lane.nland] at h
  rcases h with h | ⟨-, h⟩
  · exact absurd h hC
  · rcases h with h | h
    · exact absurd h (by norm_num)
    · obtain ⟨hrt, hall⟩ := hI.2 hC
      rw [Lane.bit_iff] at h
      exact ⟨rt, hrt, (hall x hx).2, (hall _ h).2⟩

theorem entWalk8_spec {ADJ P : ℕ} (hP : ∀ g, P.testBit g = true ↔ g ∈ S)
    (hadj : ∀ g ∈ S, ∀ pa ∈ S, (fld ADJ 240 g).testBit pa = true → iform (vec pa) (vec g) ≠ 0) :
    ∀ c rest acc C rt NB, WInv8 vec S ph acc C rt → entWalk8 ADJ ph P 0 c rest acc C rt NB = true →
      ∀ g ∈ S, Good8 vec S ph g := by
  intro c
  induction c with
  | zero =>
    intro rest acc C rt NB hI h
    change CFSG.TcRes.TK.andB (finOK ph P 0 C rt NB) (Nat.beq acc P) = true at h
    rw [Lane.andB_eq_true, Lane.beq_eq_true] at h
    obtain ⟨hfin, rfl⟩ := h
    intro g hg
    rcases (hI.1 g ((hP g).2 hg)).2 with h | h
    · exact finOK_close8 hfin hI g h
    · exact h
  | succ c ih =>
    intro rest acc C rt NB hI h
    rw [entWalk8_succ] at h
    simp only [Lane.andB_eq_true, Lane.notB_eq_true, Lane.boolRec_true, Lane.beq_eq_true,
      Lane.beq_eq_false] at h
    obtain ⟨hPg, hacc, hroot, hnon⟩ := h
    rw [Lane.bit_iff, hP] at hPg
    by_cases hgp : (rest &&& 255) = ((rest >>> 8) &&& 255)
    · obtain ⟨hfin, hw⟩ := hroot hgp
      refine ih _ _ _ _ _ ⟨fun x hx => ?_, fun _ => ⟨hPg, fun x hx => ?_⟩⟩ hw
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨hxS, hx'⟩ := hI.1 x hx
          refine ⟨hxS, Or.inr ?_⟩
          rcases hx' with hx' | hx'
          · exact finOK_close8 hfin hI x hx'
          · exact hx'
        · exact ⟨hPg, Or.inl (by rw [pow_testBit, decide_eq_true rfl])⟩
      · rw [pow_testBit, decide_eq_true_eq] at hx
        subst hx
        exact ⟨by rw [testBit_or_pow]; simp, Relation.ReflTransGen.refl⟩
    · obtain ⟨hCpa, hag, hw⟩ := hnon hgp
      rw [Lane.bit_iff] at hCpa hag
      have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at hCpa
        exact absurd hCpa (by decide)
      obtain ⟨hrt, hall⟩ := hI.2 hC
      have hpaS : ((rest >>> 8) &&& 255) ∈ S := (hI.1 _ (hall _ hCpa).1).1
      refine ih _ _ _ _ _ ⟨fun x hx => ?_, fun _ => ⟨hrt, fun x hx => ?_⟩⟩ hw
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨hxS, hx'⟩ := hI.1 x hx
          refine ⟨hxS, ?_⟩
          rcases hx' with hx' | hx'
          · exact Or.inl (by rw [testBit_or_pow, hx']; rfl)
          · exact Or.inr hx'
        · exact ⟨hPg, Or.inl (by rw [testBit_or_pow]; simp)⟩
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨h1, h2⟩ := hall x hx
          exact ⟨by rw [testBit_or_pow, h1]; rfl, h2⟩
        · refine ⟨by rw [testBit_or_pow]; simp, ?_⟩
          exact Relation.ReflTransGen.tail (hall _ hCpa).2
            ⟨hpaS, hPg, hadj _ hPg _ hpaS hag⟩

end Walk8

theorem pl5Rec_of_checks {vec : ℕ → Fin Tag.E8.rank → ℤ} {rt : ℕ → ℕ → ℕ} {neg : ℕ → ℕ}
    {V ADJ PW e : ℕ} {RC BS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hD : DatumRaw Tag.E8 240 vec rt (fun g v => Nat.beq (fld (fld ADJ 240 g) 1 v) 1) neg)
    (hrc : ∀ g < 240, rc5OK RC V g = true) (hpl : pl5OK RC BS ADJ PW e = true)
    (hmv : Nat.land (Nat.shiftRight e 21) 1 = 0) :
    ∀ g ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
        (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))),
      ∃ r ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
        (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))),
      Relation.ReflTransGen (fun a b =>
        a ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
          (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))) ∧
        b ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
          (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))) ∧
        iform (vec a) (vec b) ≠ 0) r g ∧
      Relation.ReflTransGen (fun a b =>
        a ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
          (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))) ∧
        b ∈ PhiP5 vec (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
          (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))) ∧
        iform (vec a) (vec b) ≠ 0) r (fld PW 8 r) := by
  simp only [pl5OK, Lane.strictB_eq] at hpl
  rw [hmv] at hpl
  have hmk := mset_kmask5 hrc (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
    (Nat.land (Nat.shiftRight e 10) 1023)
  have hlt := kmask5_lt hrc (BS (Nat.land (Nat.shiftRight e 20) 1)) (Nat.land e 1023)
    (Nat.land (Nat.shiftRight e 10) 1023)
  subst hvec
  refine entWalk8_spec (S := PhiP5 (vecOf 8 V)
      (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land e 1023)))
      (lam (BS (Nat.land (Nat.shiftRight e 20) 1)) (v5 (Nat.land (Nat.shiftRight e 10) 1023))))
    (fun g => ?_) (fun g hg pa hpa h => ?_) _ _ 0 0 0 0
    ⟨fun x hx => by rw [Nat.zero_testBit] at hx; exact absurd hx (by decide),
      fun h => absurd rfl h⟩ hpl
  · rw [← hmk]
    change _ ↔ g < 240 ∧ bit _ g = true
    rw [Lane.bit_iff]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hg
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
      exact absurd h (by decide)
    · exact fun h => h.2
  · have := (hD.adj g hg.1 pa hpa.1).1
    apply this
    rw [Lane.beq_eq_true, Lane.fld_one_eq_one]
    exact h

end CFSG.KC.TcRes

end
