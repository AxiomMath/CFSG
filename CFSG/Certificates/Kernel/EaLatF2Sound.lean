module

public import Certificates.Data.Kernel.EaLatF2
public import CFSG.Certificates.Kernel.AxisPlane.Pop
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Sporadic.HS.SmallF2Spec

public section

set_option maxHeartbeats 400000

namespace CFSG.KC.EaLat.F2

open CFSG.KC.EaLat CFSG.KC.Misc.Spec CFSG.Sporadic.SmallF2 CFSG.KC.AxisPlane
open scoped Matrix

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem shl1 (l : ℕ) : Nat.shiftLeft (nat_lit 1) l = 2 ^ l :=
  (Nat.shiftLeft_eq 1 l).trans (Nat.one_mul _)

theorem sub1 (N : ℕ) : Nat.sub N (nat_lit 1) = N - 1 := rfl

theorem natRec_succ {z : ℕ} {s : ℕ → ℕ → ℕ} (m : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) z s (m + 1) : ℕ) = s m (Nat.rec (motive := fun _ => ℕ) z s m) :=
  rfl

theorem full2048_eq : full2048 = 2 ^ 2048 - 1 := by
  unfold full2048
  rw [shl1, sub1]

theorem testBit_full (q : ℕ) : full2048.testBit q = decide (q < 2048) := by
  rw [full2048_eq, Nat.testBit_two_pow_sub_one]

theorem bit_eq (m i : ℕ) : bit m i = m.testBit i := by
  unfold bit
  rw [shl1, Bool.eq_iff_iff, Nat.blt_eq]
  change 0 < m &&& 2 ^ i ↔ _
  rw [Nat.and_two_pow]
  cases m.testBit i <;> simp

theorem testBit_fld (M o c : ℕ) :
    (fld M o 2047).testBit c = (decide (c < 11) && M.testBit (o + c)) := by
  unfold fld
  change ((M >>> o) &&& 2047).testBit c = _
  have e : (2047 : ℕ) = 2 ^ 11 - 1 := by norm_num
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem w_eq {l : ℕ} (hl : l < 11) : 2048 = (2 ^ l + 2 ^ l) * 2 ^ (10 - l) := by
  have e : l + 1 + (10 - l) = 11 := by omega
  rw [← two_mul, ← pow_succ', ← pow_add, e]
  norm_num

theorem lt_pow_dbl (b : ℕ) : 2 ^ b - 1 < 2 ^ (b + b) :=
  lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos b) Nat.one_pos)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem testBit_planeK {l : ℕ} (hl : l < 11) (q : ℕ) :
    (planeK l).testBit q = (decide (q < 2048) && q.testBit l) := by
  have hb : planeK l = ((2 ^ 2 ^ l - 1) <<< 2 ^ l) * (full2048 / (2 ^ (2 ^ l + 2 ^ l) - 1)) := by
    unfold planeK
    rw [letN_eq, shl1, shl1, shl1]
    rfl
  have hc : (2 ^ 2 ^ l - 1) <<< 2 ^ l < 2 ^ (2 ^ l + 2 ^ l) := by
    rw [Nat.shiftLeft_eq, pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      (Nat.two_pow_pos _)
  rw [hb, full2048_eq, CFSG.KC.Benes.testBit_mul_div (by positivity) (w_eq hl) hc]
  congr 1
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.testBit_eq_decide_div_mod_eq]
  have hm : q % (2 ^ l + 2 ^ l) = q % 2 ^ l + 2 ^ l * (q / 2 ^ l % 2) := by
    rw [← Nat.mul_two, Nat.mod_mul]
  have h1 := Nat.mod_lt q (Nat.two_pow_pos l)
  have h2 := Nat.mod_lt (q / 2 ^ l) two_pos
  rw [hm]
  generalize q % 2 ^ l = u at h1 ⊢
  generalize q / 2 ^ l % 2 = t at h2 ⊢
  generalize 2 ^ l = b at h1 ⊢
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    decide_eq_true_iff]
  interval_cases t <;> omega

@[expose] noncomputable def colR (M c m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (planeK j))
      (bit (fld M (Nat.mul (nat_lit 11) j) (nat_lit 2047)) c)) m

theorem colR_succ (M c m : ℕ) : colR M c (m + 1) = Bool.rec (motive := fun _ => Nat) (colR M c m)
    (Nat.xor (colR M c m) (planeK m)) (bit (fld M (Nat.mul (nat_lit 11) m) (nat_lit 2047)) c) :=
  rfl

theorem testBit_colR (M c : ℕ) (hc : c < 11) (q : ℕ) (hq : q < 2048) : ∀ m, m ≤ 11 →
    (colR M c m).testBit q = xsum (fun j => M.testBit (11 * j + c) && q.testBit j) m := by
  intro m hm
  induction m with
  | zero => simp [xsum, colR]
  | succ m ih =>
    rw [colR_succ, xsum, ← ih (by omega), bit_eq, testBit_fld]
    have e : Nat.mul 11 m + c = 11 * m + c := rfl
    rw [e, decide_eq_true hc, Bool.true_and]
    cases M.testBit (11 * m + c)
    · simp only [Bool.false_and, Bool.xor_false]
    · change (_ ^^^ planeK m).testBit q = _
      rw [Nat.testBit_xor, testBit_planeK (by omega), decide_eq_true hq, Bool.true_and]

theorem testBit_colK (M c : ℕ) (hc : c < 11) (q : ℕ) (hq : q < 2048) :
    (colK M c).testBit q = xsum (fun j => M.testBit (11 * j + c) && q.testBit j) 11 := by
  have e : colK M c = colR M c 11 := rfl
  rw [e]
  exact testBit_colR M c hc q hq 11 le_rfl

@[expose] noncomputable def fixR (M m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) full2048
    (fun c acc => Nat.land acc (Nat.xor full2048 (Nat.xor (colK M c) (planeK c)))) m

theorem fixR_succ (M m : ℕ) : fixR M (m + 1) =
    Nat.land (fixR M m) (Nat.xor full2048 (Nat.xor (colK M m) (planeK m))) := rfl

theorem testBit_fixR (M q : ℕ) (hq : q < 2048) : ∀ m, m ≤ 11 →
    ((fixR M m).testBit q = true ↔ ∀ c < m, (colK M c).testBit q = q.testBit c) := by
  intro m hm
  induction m with
  | zero => simp [fixR, testBit_full, hq]
  | succ m ih =>
    rw [fixR_succ]
    change (_ &&& (full2048 ^^^ (colK M m ^^^ planeK m))).testBit q = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, testBit_full,
      testBit_planeK (by omega), decide_eq_true hq, Bool.true_and, Bool.and_eq_true,
      ih (by omega)]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact h1 c hc
      · revert h2
        cases (colK M c).testBit q <;> cases q.testBit c <;> simp
    · intro h
      refine ⟨fun c hc => h c (by omega), ?_⟩
      rw [h m (by omega)]
      cases q.testBit m <;> simp

theorem fixK_iff (M x : ℕ) (hx : x < 2048) :
    (fixK M).testBit x = true ↔ toVecD 11 x ᵥ* pkMat 11 M = toVecD 11 x := by
  have h1 : (fixK M).testBit x = true ↔ ∀ c < 11, (colK M c).testBit x = x.testBit c := by
    have e : fixK M = fixR M 11 := rfl
    rw [e]
    exact testBit_fixR M x hx 11 le_rfl
  rw [h1, funext_iff]
  have h2 : ∀ c : Fin 11, (toVecD 11 x ᵥ* pkMat 11 M) c =
      if xsum (fun j => M.testBit (11 * j + c.val) && x.testBit j) 11 then 1 else 0 := by
    intro c
    rw [zmod2_xsum, Matrix.vecMul, dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun k => if M.testBit (11 * k + c.val) && x.testBit k then (1 : ZMod 2) else 0) 11]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [toVecD_apply, pkMat, Matrix.of_apply]
    cases x.testBit j.val <;> cases M.testBit (11 * j.val + c.val) <;> simp
  constructor
  · intro h c
    rw [h2, toVecD_apply, ← testBit_colK M c c.isLt x hx, h c c.isLt]
  · intro h c hc
    have e := h ⟨c, hc⟩
    rw [h2, toVecD_apply, ← testBit_colK M c hc x hx] at e
    revert e
    cases (colK M c).testBit x <;> cases x.testBit c <;> simp

theorem testBit_lowK {s : ℕ} (hs : s < 11) (q : ℕ) :
    (lowK s).testBit q = (decide (q < 2048) && decide (q % (2 ^ s + 2 ^ s) < 2 ^ s)) := by
  have hb : lowK s = (2 ^ 2 ^ s - 1) * (full2048 / (2 ^ (2 ^ s + 2 ^ s) - 1)) := by
    unfold lowK
    rw [letN_eq, shl1, shl1, shl1]
    rfl
  rw [hb, full2048_eq, CFSG.KC.Benes.testBit_mul_div (by positivity) (w_eq hs) (lt_pow_dbl _),
    Nat.testBit_two_pow_sub_one]

theorem step_lanes {s n : ℕ} (hs : s < 11) (hn : 2 ^ s * (2 * n) = 2048) (x : ℕ) :
    Nat.add (Nat.land (lanes (2 ^ s) (cnt x s) (2 * n)) (lowK s))
      (Nat.land (Nat.shiftRight (lanes (2 ^ s) (cnt x s) (2 * n)) (2 ^ s)) (lowK s)) =
      lanes (2 ^ (s + 1)) (cnt x (s + 1)) n := by
  have hw : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2w : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
  have hM : ∀ q, (lowK s).testBit q =
      (decide (q < 2 ^ (s + 1) * n) && decide (q % 2 ^ (s + 1) < 2 ^ s)) := by
    intro q
    have hW : 2 ^ (s + 1) * n = 2048 := by rw [h2w, ← hn]; ring
    rw [testBit_lowK hs, hW, h2w, two_mul]
  have hf : ∀ i < 2 * n, cnt x s i < 2 ^ 2 ^ s := fun i _ => cnt_lt x s i
  have hg : ∀ i < n, cnt x s (2 * i) < 2 ^ 2 ^ (s + 1) := fun i _ =>
    Nat.lt_of_lt_of_le (cnt_lt x s _)
      (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hg' : ∀ i < n, cnt x s (2 * i + 1) < 2 ^ 2 ^ (s + 1) := fun i _ =>
    Nat.lt_of_lt_of_le (cnt_lt x s _)
      (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hcb : ∀ i, cnt x s i < 2 ^ 2 ^ s := cnt_lt x s
  have hA : Nat.land (lanes (2 ^ s) (cnt x s) (2 * n)) (lowK s) =
      lanes (2 ^ (s + 1)) (fun i => cnt x s (2 * i)) n := by
    apply Nat.eq_of_testBit_eq
    intro q
    change (lanes (2 ^ s) (cnt x s) (2 * n) &&& lowK s).testBit q = _
    rw [Nat.testBit_and, testBit_lanes hw _ hf, hM, testBit_lanes (Nat.two_pow_pos _) _ hg, h2w]
    generalize cnt x s = f at hcb ⊢
    generalize 2 ^ s = w at hw hcb ⊢
    have hk := Nat.div_add_mod q (2 * w)
    generalize q / (2 * w) = k at hk
    have hr : q % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
    generalize q % (2 * w) = r at hk hr
    subst hk
    have e0 : w * (2 * n) = 2 * w * n := by ring
    rw [e0]
    by_cases hrw : r < w
    · have e1 : (2 * w * k + r) / w = 2 * k := by
        rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_div_left _ _ hw,
          Nat.div_eq_of_lt hrw, Nat.zero_add]
      have e2 : (2 * w * k + r) % w = r := by
        rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrw]
      rw [e1, e2, decide_eq_true hrw]
      cases decide (2 * w * k + r < 2 * w * n) <;> simp
    · have hz : (f (2 * k)).testBit r = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (hcb _) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hrw, hz]
  have hB : Nat.land (Nat.shiftRight (lanes (2 ^ s) (cnt x s) (2 * n)) (2 ^ s)) (lowK s) =
      lanes (2 ^ (s + 1)) (fun i => cnt x s (2 * i + 1)) n := by
    apply Nat.eq_of_testBit_eq
    intro q
    change ((lanes (2 ^ s) (cnt x s) (2 * n) >>> 2 ^ s) &&& lowK s).testBit q = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lanes hw _ hf, hM,
      testBit_lanes (Nat.two_pow_pos _) _ hg', h2w]
    generalize cnt x s = f at hcb ⊢
    generalize 2 ^ s = w at hw hcb ⊢
    have hk := Nat.div_add_mod q (2 * w)
    generalize q / (2 * w) = k at hk
    have hr : q % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
    generalize q % (2 * w) = r at hk hr
    subst hk
    have e0 : w * (2 * n) = 2 * w * n := by ring
    rw [e0]
    by_cases hrw : r < w
    · have e1 : (w + (2 * w * k + r)) / w = 2 * k + 1 := by
        rw [show w + (2 * w * k + r) = r + w * (2 * k + 1) by ring, Nat.add_mul_div_left _ _ hw,
          Nat.div_eq_of_lt hrw, Nat.zero_add]
      have e2 : (w + (2 * w * k + r)) % w = r := by
        rw [show w + (2 * w * k + r) = r + w * (2 * k + 1) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrw]
      have hiff : (w + (2 * w * k + r) < 2 * w * n) ↔ (2 * w * k + r < 2 * w * n) := by
        constructor
        · intro h
          omega
        · intro h
          have hkn : k < n := by
            by_contra hc
            have : 2 * w * n ≤ 2 * w * k := Nat.mul_le_mul_left _ (by omega)
            omega
          have h3 : 2 * w * (k + 1) ≤ 2 * w * n := Nat.mul_le_mul_left _ hkn
          rw [Nat.mul_succ] at h3
          omega
      rw [e1, e2, decide_eq_true hrw, decide_eq_decide.2 hiff]
      cases decide (2 * w * k + r < 2 * w * n) <;> simp
    · have hz : (f (2 * k + 1)).testBit r = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (hcb _) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hrw, hz]
  rw [hA, hB, CFSG.KC.Benes.nadd, lanes_add]
  congr 1
  funext i
  rw [cnt_succ]

set_option exponentiation.threshold 2048 in
theorem lanes0 {x : ℕ} (hx : x < 2 ^ 2048) : x = lanes (2 ^ 0) (cnt x 0) (2 ^ (11 - 0)) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_lanes (w := 2 ^ 0) (f := cnt x 0) (Nat.two_pow_pos 0) (2 ^ (11 - 0))
    (fun i _ => cnt_lt x 0 i)]
  simp only [pow_zero, Nat.div_one, Nat.mod_one, cnt_zero, Nat.one_mul, Nat.sub_zero]
  by_cases hq : q < 2 ^ 11
  · rw [decide_eq_true hq, Bool.true_and]
    cases x.testBit q <;> rfl
  · rw [decide_eq_false hq, Bool.false_and]
    have h2 : 2048 ≤ q := by
      have h3 := Nat.not_lt.1 hq
      norm_num at h3
      exact h3
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos h2))

theorem popR_lanes {x : ℕ} (hx : x < 2 ^ 2048) : ∀ s, s ≤ 11 →
    Nat.rec (motive := fun _ => Nat) x (fun l acc => letN acc fun y => letN (lowK l) fun m =>
      Nat.add (Nat.land y m) (Nat.land (Nat.shiftRight y (Nat.shiftLeft (nat_lit 1) l)) m)) s =
      lanes (2 ^ s) (cnt x s) (2 ^ (11 - s))
  | 0, _ => lanes0 hx
  | s + 1, hs => by
    refine (natRec_succ s).trans ?_
    beta_reduce
    rw [letN_eq, letN_eq, shl1, popR_lanes hx s (by omega)]
    have e : 2 ^ (11 - s) = 2 * 2 ^ (11 - (s + 1)) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [e]
    refine step_lanes (by omega) ?_ x
    rw [← e, ← Nat.pow_add, Nat.add_sub_of_le (by omega : s ≤ 11)]

theorem popK_eq {x : ℕ} (hx : x < 2 ^ 2048) :
    popK x = ((Finset.range 2048).filter fun q => x.testBit q = true).card := by
  have h : popK x = lanes (2 ^ 11) (cnt x 11) (2 ^ (11 - 11)) := popR_lanes hx 11 le_rfl
  rw [h, Finset.card_filter]
  simp only [Nat.sub_self, pow_zero, lanes, Nat.mul_zero, Nat.zero_add, Nat.one_mul, cnt]
  refine Finset.sum_congr (by norm_num) fun j _ => ?_
  cases x.testBit j <;> rfl

end CFSG.KC.EaLat.F2

end
