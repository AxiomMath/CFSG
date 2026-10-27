module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneSim
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BabyMonster.DyLaneTree
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Ln

set_option exponentiation.threshold 140000

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

theorem lnEqL_sound : ∀ {a b : List ℕ}, lnEqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    rw [Nat.eq_of_beq_eq_true h1, lnEqL_sound h2]

theorem lnEqLL_sound : ∀ {a b : List (List ℕ)}, lnEqLL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    rw [lnEqL_sound h1, lnEqLL_sound h2]

theorem KKOK_lnKK : KKOK lnKK 4 := by
  intro l hl
  interval_cases l <;> rfl

theorem fld_lnFail : fld lnFail 4371 = 512 := by
  change fld (512 <<< 69936) 4371 = 512
  rw [Nat.shiftLeft_eq, show 69936 = 16 * 4371 by rfl, fld_mul_pow, ite_eq_left le_rfl, Nat.sub_self]
  rfl

theorem lnFail_lt : lnFail < 2 ^ (16 * 8192) := by
  change 512 <<< 69936 < _
  rw [Nat.shiftLeft_eq, show (512 : ℕ) = 2 ^ 9 from rfl, ← Nat.pow_add]
  exact Nat.pow_lt_pow_right (by decide) (by decide)

theorem fld_parity {r : ℕ} (hr : r < 2 ^ 4371) (j q : ℕ) :
    fld (lnSpr (lnKs 1 16) (lnD 1 16) (r >>> j) <<< 8) q = if r.testBit (j + q) then 256 else 0 := by
  have hx : r >>> j < 2 ^ (8192 * 1) := lt_of_le_of_lt (Nat.shiftRight_le _ _)
    (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by decide)))
  have hs := testBit_spr (w := 1) (W := 16) (by decide) (by decide) hx
  have hf : ∀ q, fld (lnSpr (lnKs 1 16) (lnD 1 16) (r >>> j)) q = if r.testBit (j + q) then 1 else 0 := by
    intro q
    apply Nat.eq_of_testBit_eq
    intro i
    rw [fld_testBit, hs]
    unfold lay
    have h01 : ∀ (c : Bool), ((if c = true then 1 else 0 : ℕ)).testBit i = (c && decide (i = 0)) := by
      intro c
      cases c
      · simp
      · simp only [ite_true, Bool.true_and]
        cases h : decide (i = 0)
        · have : i ≠ 0 := by simpa using h
          exact Bool.eq_false_iff.2 (fun h' => this (Nat.testBit_one_eq_true_iff_self_eq_zero.1 h'))
        · have : i = 0 := by simpa using h
          rw [this]
          rfl
    rw [h01]
    by_cases hi : i < 16
    · rw [decide_eq_true hi, Bool.true_and, Nat.mul_add_mod, Nat.mod_eq_of_lt hi,
        Nat.mul_add_div (by decide), Nat.div_eq_of_lt hi, Nat.add_zero, Nat.mul_one,
        Nat.testBit_shiftRight]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [Nat.add_zero]
        cases r.testBit (j + q) <;> rfl
      · rw [decide_eq_false (by omega), Bool.false_and, decide_eq_false (by omega), Bool.and_false]
    · rw [decide_eq_false hi, Bool.false_and, decide_eq_false (by omega), Bool.and_false]
  rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mul_comm,
    fld_mul _ (fun f => by rw [hf]; split <;> omega), hf]
  split <;> simp

theorem and_one_eq (x : ℕ) : x &&& 1 = if x.testBit 0 then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem testBit8 {a : ℕ} (ha : a < 256) (c : Bool) : (a + if c then 256 else 0).testBit 8 = c := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases c
  · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    rw [Nat.div_eq_of_lt (by exact ha)]
    rfl
  · simp only [ite_true]
    rw [show (2 : ℕ) ^ 8 = 256 from rfl, show a + 256 = a + 256 * 1 by ring, Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt ha]
    rfl

theorem leaf_ok {e : ℕ} (he : e ≤ 8) {F R : ℕ → ℕ} {B j i : ℕ} (hB : B ≤ 2 ^ (16 * 4371)) :
    lnLeaf (2 ^ e) (lnKs 1 16) F R B j i < 2 ^ (16 * 8192) ∧
    (fld (lnLeaf (2 ^ e) (lnKs 1 16) F R B j i) 4371 = 0 →
      F i < B ∧ R i < 2 ^ 4371 ∧ (∀ q, fld (F i) q < 2 ^ e) ∧
      ∀ q, fld (lnLeaf (2 ^ e) (lnKs 1 16) F R B j i) q =
        fld (F i) q + if (R i).testBit (j + q) then 256 else 0) := by
  unfold lnLeaf
  cases hc : andB (andB (Nat.beq (Nat.land (F i) (dyMask (2 ^ e))) (F i)) (Nat.blt (F i) B))
      (Nat.blt (R i) (Nat.shiftLeft (nat_lit 1) (nat_lit 4371)))
  · refine ⟨lnFail_lt, fun h => ?_⟩
    change fld lnFail 4371 = 0 at h
    rw [fld_lnFail] at h
    exact absurd h (by decide)
  · obtain ⟨hc1, hc3⟩ := andB_true hc
    obtain ⟨hc1, hc2⟩ := andB_true hc1
    have hF : F i &&& dyMask (2 ^ e) = F i := Nat.eq_of_beq_eq_true hc1
    have hFB : F i < B := Nat.le_of_ble_eq_true hc2
    have hR : R i < 2 ^ 4371 := by
      have : R i < Nat.shiftLeft (nat_lit 1) (nat_lit 4371) := Nat.le_of_ble_eq_true hc3
      rwa [shl_one] at this
    have hFf : ∀ q, fld (F i) q < 2 ^ e := fun q => by
      rw [← hF, fld_land_dyMask (by omega)]
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos e)
      · exact Nat.two_pow_pos e
    have hfields : ∀ q, fld (Nat.add (F i) (Nat.shiftLeft (lnSpr (lnKs 1 16) (lnD 1 16)
        (Nat.shiftRight (R i) j)) 8)) q = fld (F i) q + if (R i).testBit (j + q) then 256 else 0 := by
      intro q
      change fld (F i + (lnSpr (lnKs 1 16) (lnD 1 16) (R i >>> j) <<< 8)) q = _
      rw [fld_add _ (fun f => by
        rw [fld_parity hR]
        have := hFf f
        have : 2 ^ e ≤ 256 := Nat.pow_le_pow_right (by decide) he
        split <;> omega), fld_parity hR]
    refine ⟨?_, fun _ => ⟨hFB, hR, hFf, hfields⟩⟩
    have hlt := lt_of_fld (x := Nat.add (F i) (Nat.shiftLeft (lnSpr (lnKs 1 16) (lnD 1 16)
        (Nat.shiftRight (R i) j)) 8)) (n := 4371) (fun q hq => by
      rw [hfields, fld_of_lt (lt_of_lt_of_le hFB hB) hq, testBit_x_ge hR (by omega)]
      rfl)
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by decide))

theorem lnSt_sound {Bs SS KK : List (List ℕ)} (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) (hSS : ∀ s < 274, lnStripOK Bs SS s = true)
    (hlen : SS.length = 274) (hKK : KK = lnKK) {e : ℕ} (he1 : 1 ≤ e) (he : e ≤ 8) {F R : ℕ → ℕ}
    {s k : ℕ} (hs : s < 274) (h : lnSt (2 ^ e) KK SS F R s k = true) :
    ∀ t < 16, dyElim (2 ^ e) Bs (16 * s) (F (16 * k + t)) = (R (16 * k + t) >>> (16 * s)) <<< (16 * s) ∧
      R (16 * k + t) < 2 ^ 4371 := by
  subst hKK
  set B := Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) (Nat.sub (nat_lit 4371) (Nat.mul (nat_lit 16) s)))
    with hBdef
  have hB' : B ≤ 2 ^ (16 * 4371) := by
    rw [hBdef, shl_one]
    exact Nat.pow_le_pow_right (by decide) (by
      change 16 * (4371 - 16 * s) ≤ _
      omega)
  set U := lnLeaf (2 ^ e) (lnKs 1 16) F R B (16 * s) with hU
  set Z := lnT lnKK U 4 (16 * k) with hZ
  have h' : andB (Nat.beq (Nat.land Z (lnMaskP (2 ^ e))) Z)
      (Nat.beq (lnElim (2 ^ e) (lnDrop s SS) (Nat.land Z (lnMask (2 ^ e)))
        (Nat.land (Nat.shiftRight Z (nat_lit 8)) lnOnes)) (nat_lit 0)) = true := h
  obtain ⟨hmask, helim⟩ := andB_true h'
  have hmask' : Z &&& lnMaskP (2 ^ e) = Z := Nat.eq_of_beq_eq_true hmask
  have hm0 : 0 < 2 ^ e := Nat.two_pow_pos e
  have hm8 : 2 ^ e ≤ 256 := Nat.pow_le_pow_right (by decide) he
  have hUb : ∀ t < 16, U (16 * k + t) < 2 ^ (16 * 8192) := fun t _ => (leaf_ok he hB').1
  have hZf : ∀ t < 16, ∀ q, fld Z (16 * q + t) = fld (U (16 * k + t)) q := fun t ht q =>
    fld_lnT4 KKOK_lnKK hUb ht q
  have hok : ∀ t < 16, fld (U (16 * k + t)) 4371 = 0 := by
    intro t ht
    rw [← hZf t ht, ← hmask', fld_land, fld_lnMaskP hm0 hm8, ite_eq_right (by omega), Nat.and_zero]
  have hleaf := fun t (ht : t < 16) => (leaf_ok (F := F) (R := R) (i := 16 * k + t) (j := 16 * s) he hB').2
    (hok t ht)
  have hrel : LnRel (2 ^ e) (16 * s) (16 * s) (fun t => R (16 * k + t)) (Nat.land Z (lnMask (2 ^ e)))
      (Nat.land (Nat.shiftRight Z (nat_lit 8)) lnOnes) (fun t => F (16 * k + t)) (fun _ => 0) := by
    refine ⟨fun t ht q => ?_, fun t ht q => ?_, fun t ht => ?_, fun t ht q => ?_, fun t ht b => ?_⟩
    · obtain ⟨hFB, -, hFf, hf⟩ := hleaf t ht
      change fld (Z &&& lnMask (2 ^ e)) _ = _
      rw [fld_land, fld_lnMask hm0 (by omega)]
      by_cases hq : q < 4371
      · rw [ite_eq_left (show 16 * q + t < 16 * 4371 by omega), hZf t ht, hf,
          Nat.and_two_pow_sub_one_eq_mod]
        split
        · rw [show fld (F (16 * k + t)) q + 256 = fld (F (16 * k + t)) q + 2 ^ e * (256 / 2 ^ e) by
            rw [Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 he : 2 ^ e ∣ 2 ^ 8)],
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hFf q)]
        · rw [Nat.add_zero, Nat.mod_eq_of_lt (hFf q)]
      · rw [ite_eq_right (show ¬ 16 * q + t < 16 * 4371 by omega), Nat.and_zero,
          fld_of_lt (lt_of_lt_of_le hFB hB') (by omega)]
    · obtain ⟨-, hR, hFf, hf⟩ := hleaf t ht
      change fld ((Z >>> 8) &&& lnOnes) _ = _
      rw [fld_land, fld_lnOnes]
      by_cases hq : q < 4371
      · have hFq := hFf q
        rw [ite_eq_left (by omega), and_one_eq, fld_testBit, Nat.testBit_shiftRight, testBit_of_fld,
          show (8 + (16 * (16 * q + t) + 0)) / 16 = 16 * q + t by omega,
          show (8 + (16 * (16 * q + t) + 0)) % 16 = 8 by omega, hZf t ht, hf q,
          testBit8 (by omega)]
        simp
      · rw [ite_eq_right (by omega), Nat.and_zero, testBit_x_ge hR (by omega)]
        rfl
    · exact lt_of_lt_of_le (hleaf t ht).1 (by rw [hBdef, shl_one]; rfl)
    · exact (hleaf t ht).2.2.1 q
    · simp
  have hsim := sim_outer hB hr hSS hlen he1 he (fun t ht => (hleaf t ht).2.1) (274 - s) s (by omega)
    le_rfl
  rw [show min (16 * s) 4371 = 16 * s by omega] at hsim
  have hrun := hsim.2 _ _ _ _ hrel (by
      rw [lnElim_eq, lnDrop_eq] at helim
      exact Nat.eq_of_beq_eq_true helim)
  intro t ht
  rw [dyElim_run hB _ (by omega)]
  exact ⟨hrun t ht, (hleaf t ht).2.1⟩

end CFSG.KC.BM.Ln

end
