module

public import Certificates.Data.Kernel.Multipliers.LabZ
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.LabZ

open CFSG.KC CFSG.KC.LceS CFSG.KC.LabZ CFSG.Certificates.LCE

@[expose] def decZ (V d : ℕ) : ℤ := ((V / 2 ^ (48 * d)) % 2 ^ 48 : ℕ) - 2 ^ 47

@[expose] noncomputable def zprod {G : Type*} [Group G] (g : ℕ → G) (D : ℕ) (v : ℕ → ℤ) : G :=
  ((List.range D).map fun d => g d ^ v d).prod

section Zprod

variable {G : Type*} [Group G] {g : ℕ → G}

private theorem zprod_succ (D : ℕ) (v : ℕ → ℤ) : zprod g (D + 1) v = zprod g D v * g D ^ v D := by
  unfold zprod
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

private theorem zprod_congr {D : ℕ} {a b : ℕ → ℤ} (h : ∀ d < D, a d = b d) :
    zprod g D a = zprod g D b := by
  induction D with
  | zero => rfl
  | succ D ih => rw [zprod_succ, zprod_succ, ih fun d hd => h d (by omega), h D (by omega)]

private theorem zprod_zero (D : ℕ) : zprod g D 0 = 1 := by
  induction D with
  | zero => rfl
  | succ D ih => rw [zprod_succ, ih, Pi.zero_apply, zpow_zero, mul_one]

private theorem commute_zprod (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (v : ℕ → ℤ) (e : ℕ)
    (k : ℤ) : Commute (zprod g D v) (g e ^ k) := by
  induction D with
  | zero => exact Commute.one_left _
  | succ D ih =>
    rw [zprod_succ]
    exact Commute.mul_left ih (Commute.zpow_zpow (hc D e) _ _)

private theorem zprod_add (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (a b : ℕ → ℤ) :
    zprod g D (a + b) = zprod g D a * zprod g D b := by
  induction D with
  | zero => exact (one_mul 1).symm
  | succ D ih =>
    rw [zprod_succ, zprod_succ, zprod_succ, ih, Pi.add_apply, zpow_add]
    have h1 : zprod g D b * g D ^ a D = g D ^ a D * zprod g D b := (commute_zprod hc D b D (a D)).eq
    calc zprod g D a * zprod g D b * (g D ^ a D * g D ^ b D)
        = zprod g D a * (zprod g D b * g D ^ a D) * g D ^ b D := by simp only [mul_assoc]
      _ = zprod g D a * (g D ^ a D * zprod g D b) * g D ^ b D := by rw [h1]
      _ = zprod g D a * g D ^ a D * (zprod g D b * g D ^ b D) := by simp only [mul_assoc]

private theorem zprod_neg (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (a : ℕ → ℤ) :
    zprod g D (-a) = (zprod g D a)⁻¹ := by
  have h := zprod_add hc D a (-a)
  rw [add_neg_cancel, zprod_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem zprod_eq_one {D : ℕ} {t : ℕ → ℤ} (h : ∀ d < D, g d ^ t d = 1) : zprod g D t = 1 := by
  induction D with
  | zero => rfl
  | succ D ih => rw [zprod_succ, ih fun d hd => h d (by omega), h D (by omega), mul_one]

private theorem zprod_eq_single {D k : ℕ} (hk : k < D) {t : ℕ → ℤ} (h1 : t k = 1)
    (h : ∀ d < D, d ≠ k → g d ^ t d = 1) : zprod g D t = g k := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [zprod_succ]
    rcases Nat.lt_or_ge k D with hkD | hkD
    · rw [ih hkD fun d hd hdk => h d (by omega) hdk, h D (by omega) (by omega), mul_one]
    · have e : k = D := by omega
      subst e
      rw [zprod_eq_one fun d hd => h d (by omega) (by omega), one_mul, h1, zpow_one]

end Zprod

private def encN (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | D + 1 => encN c D + c D * 2 ^ (48 * D)

private theorem encN_congr {c c' : ℕ → ℕ} : ∀ {D : ℕ}, (∀ d < D, c d = c' d) → encN c D = encN c' D
  | 0, _ => rfl
  | D + 1, h => by
    rw [encN, encN, encN_congr fun d hd => h d (by omega), h D (by omega)]

private theorem encN_add (c c' : ℕ → ℕ) : ∀ D, encN c D + encN c' D = encN (fun d => c d + c' d) D
  | 0 => rfl
  | D + 1 => by
    rw [encN, encN, encN, ← encN_add c c' D]
    ring

private theorem p48 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num

private theorem encN_lt {c : ℕ → ℕ} : ∀ {D : ℕ}, (∀ d < D, c d < 2 ^ 48) → encN c D < 2 ^ (48 * D)
  | 0, _ => by simp [encN]
  | D + 1, h => by
    have ih := encN_lt (D := D) fun d hd => h d (by omega)
    have hc := h D (by omega)
    rw [encN]
    calc encN c D + c D * 2 ^ (48 * D) < 2 ^ (48 * D) + c D * 2 ^ (48 * D) :=
          Nat.add_lt_add_right ih _
      _ = (c D + 1) * 2 ^ (48 * D) := by ring
      _ ≤ 2 ^ 48 * 2 ^ (48 * D) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (48 * (D + 1)) := by ring

private theorem encN_digit {c : ℕ → ℕ} : ∀ {D : ℕ}, (∀ d < D, c d < 2 ^ 48) → ∀ e < D,
    encN c D / 2 ^ (48 * e) % 2 ^ 48 = c e
  | 0, _, e, he => absurd he (Nat.not_lt_zero e)
  | D + 1, h, e, he => by
    have hlt := encN_lt (D := D) fun d hd => h d (by omega)
    have ih := encN_digit (D := D) fun d hd => h d (by omega)
    rw [encN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt he
      have e1 : c D * 2 ^ (48 * D) = 2 ^ (48 * e) * (2 ^ 48 * (c D * 2 ^ (48 * k))) := by
        rw [hk]
        ring
      rw [e1, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih e he
    · rw [Nat.mul_comm (c e), Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt,
        zero_add, Nat.mod_eq_of_lt (h e (by omega))]

private theorem encN_mod (n : ℕ) : ∀ D, n % 2 ^ (48 * D) = encN (fun e => n / 2 ^ (48 * e) % 2 ^ 48) D
  | 0 => by simp [encN, Nat.mod_one]
  | D + 1 => by
    rw [encN, ← encN_mod n D, show 48 * (D + 1) = 48 * D + 48 by ring, pow_add, Nat.mod_mul]
    ring

private theorem digit_and (a b k : ℕ) :
    (a &&& b) / 2 ^ k % 2 ^ 48 = (a / 2 ^ k % 2 ^ 48) &&& (b / 2 ^ k % 2 ^ 48) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (i < 48) <;> simp

private theorem lt_of_land_high {t : ℕ} (ht : t < 2 ^ 48) (h : t &&& 281474943156224 = 0) :
    t < 2 ^ 25 := by
  have e : t = t &&& (281474943156224 ||| (2 ^ 25 - 1)) := by
    rw [show (281474943156224 ||| (2 ^ 25 - 1) : ℕ) = 2 ^ 48 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ht]
  calc t = t &&& (281474943156224 ||| (2 ^ 25 - 1)) := e
    _ = t % 2 ^ 25 := by
      rw [Nat.and_or_distrib_left, h, Nat.zero_or, Nat.and_two_pow_sub_one_eq_mod]
    _ < 2 ^ 25 := Nat.mod_lt _ (by positivity)

private theorem lanes_eq (v : ℕ) : ∀ D, lanes D v = encN (fun _ => v) D
  | 0 => rfl
  | D + 1 => by
    change Nat.add (lanes D v) (Nat.shiftLeft v (Nat.mul 48 D)) = _
    rw [encN, ← lanes_eq v D]
    change lanes D v + v <<< (48 * D) = _
    rw [Nat.shiftLeft_eq]

private theorem encN_single (a h : ℕ) : ∀ D, h < D →
    encN (fun d => if d = h then a + 1 else a) D = encN (fun _ => a) D + 2 ^ (48 * h)
  | 0, hh => absurd hh (Nat.not_lt_zero h)
  | D + 1, hh => by
    have ih := encN_single a h D
    rw [encN, encN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | hh
    · rw [ih hh, ite_eq_right (by omega)]
      ring
    · subst hh
      rw [encN_congr (c' := fun _ => a) (fun d hd => ite_eq_right (by omega)), ite_eq_left rfl]
      ring

private def Lab (D S : ℕ) (c : ℕ → ℕ) (k : ℕ) : Prop :=
  S = encN c D ∧ ∀ d < D, 140737488355328 ≤ c d + k * 16777216 ∧ c d ≤ 140737488355328 + k * 16777216

private def vec (c : ℕ → ℕ) : ℕ → ℤ := fun d => (c d : ℤ) - 2 ^ 47

private theorem vec_const : vec (fun _ => 140737488355328) = 0 := by
  funext d
  simp only [vec, Pi.zero_apply]
  norm_num

private theorem lab_addF {D S x k BIAS : ℕ} {c c' : ℕ → ℕ} (hS : Lab D S c k) (hx : Lab D x c' 1)
    (hk : k < 4096) (hB : BIAS = encN (fun _ => 140737488355328) D) :
    Lab D (addF BIAS S x) (fun d => c d + c' d - 140737488355328) (k + 1) ∧
      ∀ d < D, vec (fun d => c d + c' d - 140737488355328) d = vec c d + vec c' d := by
  obtain ⟨rfl, hc⟩ := hS
  obtain ⟨rfl, hc'⟩ := hx
  subst hB
  have hle : ∀ d < D, 140737488355328 ≤ c d + c' d := fun d hd => by
    have := hc d hd
    have := hc' d hd
    omega
  refine ⟨⟨?_, fun d hd => by have := hc d hd; have := hc' d hd; dsimp only; omega⟩, fun d hd => ?_⟩
  · change encN c D + encN c' D - encN (fun _ => 140737488355328) D = _
    rw [encN_add, encN_congr (c := fun d => c d + c' d)
      (c' := fun d => (c d + c' d - 140737488355328) + 140737488355328)
      (fun d hd => by have := hle d hd; omega), ← encN_add, Nat.add_sub_cancel]
  · simp only [vec]
    rw [Nat.cast_sub (hle d hd)]
    push_cast
    ring

private theorem lab_addB {D S x k BIAS : ℕ} {c c' : ℕ → ℕ} (hS : Lab D S c k) (hx : Lab D x c' 1)
    (hk : k < 4096) (hB : BIAS = encN (fun _ => 140737488355328) D) :
    Lab D (addB BIAS S x) (fun d => c d + 140737488355328 - c' d) (k + 1) ∧
      ∀ d < D, vec (fun d => c d + 140737488355328 - c' d) d = vec c d - vec c' d := by
  obtain ⟨rfl, hc⟩ := hS
  obtain ⟨rfl, hc'⟩ := hx
  subst hB
  have hle : ∀ d < D, c' d ≤ c d + 140737488355328 := fun d hd => by
    have := hc d hd
    have := hc' d hd
    omega
  refine ⟨⟨?_, fun d hd => by have := hc d hd; have := hc' d hd; dsimp only; omega⟩, fun d hd => ?_⟩
  · change encN c D + encN (fun _ => 140737488355328) D - encN c' D = _
    rw [encN_add, encN_congr (c := fun d => c d + 140737488355328)
      (c' := fun d => (c d + 140737488355328 - c' d) + c' d)
      (fun d hd => by have := hle d hd; omega), ← encN_add, Nat.add_sub_cancel]
  · simp only [vec]
    rw [Nat.cast_sub (hle d hd)]
    push_cast
    ring

private theorem lab_digit {D S k : ℕ} {c : ℕ → ℕ} (h : Lab D S c k) (hk : k < 4096) {e : ℕ}
    (he : e < D) : S / 2 ^ (48 * e) % 2 ^ 48 = c e := by
  obtain ⟨rfl, hc⟩ := h
  exact encN_digit (fun d hd => by have := hc d hd; rw [p48]; omega) e he

private theorem decZ_lab {D S k : ℕ} {c : ℕ → ℕ} (h : Lab D S c k) (hk : k < 4096) {e : ℕ}
    (he : e < D) : decZ S e = vec c e := by
  unfold decZ
  rw [lab_digit h hk he]
  rfl

private theorem lab_unique {D S k k' : ℕ} {c c' : ℕ → ℕ} (h : Lab D S c k) (h' : Lab D S c' k')
    (hk : k < 4096) (hk' : k' < 4096) : ∀ d < D, vec c d = vec c' d := by
  intro d hd
  rw [← decZ_lab h hk hd, ← decZ_lab h' hk' hd]

private theorem lab_bias {D BIAS : ℕ} (hB : BIAS = encN (fun _ => 140737488355328) D) (k : ℕ) :
    Lab D BIAS (fun _ => 140737488355328) k :=
  ⟨hB, fun _ _ => by dsimp only; omega⟩

private theorem lab_single {D BIAS h : ℕ} (hB : BIAS = encN (fun _ => 140737488355328) D)
    (hh : h < D) :
    Lab D (BIAS + 2 ^ (48 * h)) (fun d => if d = h then 140737488355328 + 1 else 140737488355328) 1 := by
  refine ⟨by rw [encN_single _ _ D hh, hB], fun d _ => ?_⟩
  dsimp only
  split_ifs <;> omega

private theorem zprod_single {G : Type*} [Group G] {g : ℕ → G} {D h : ℕ} (hh : h < D) :
    zprod g D (vec fun d => if d = h then 140737488355328 + 1 else 140737488355328) = g h := by
  refine zprod_eq_single hh ?_ fun d _ hdh => ?_
  · simp only [vec, ↓reduceIte]
    norm_num
  · simp only [vec, hdh, ↓reduceIte]
    norm_num

private theorem valid_lab {D BIAS Q HIGH TOP x : ℕ} (hc : constsOK D BIAS Q HIGH TOP = true)
    (hv : validZ BIAS Q HIGH TOP x = true) : ∃ c, Lab D x c 1 := by
  unfold constsOK at hc
  simp only [LceP.andB_iff, Nat.beq_eq] at hc
  obtain ⟨-, hB, hQ, hH, hT⟩ := hc
  rw [lanes_eq] at hB hQ hH
  unfold validZ at hv
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  change BIAS ≤ x + Q at h1
  change x + Q - BIAS < TOP at h2
  change (x + Q - BIAS) &&& HIGH = 0 at h3
  have hT' : TOP = 2 ^ (48 * D) := by
    rw [hT]
    change 1 <<< (48 * D) = _
    rw [Nat.shiftLeft_eq, one_mul]
  rw [hT'] at h2
  set T := x + Q - BIAS with hTdef
  set t : ℕ → ℕ := fun e => T / 2 ^ (48 * e) % 2 ^ 48 with htdef
  have hTt : T = encN t D := by rw [← encN_mod, Nat.mod_eq_of_lt h2]
  have ht25 : ∀ e < D, t e < 2 ^ 25 := by
    intro e he
    have hd := digit_and T HIGH (48 * e)
    rw [h3, Nat.zero_div, Nat.zero_mod, hH,
      encN_digit (c := fun _ => 281474943156224) (fun _ _ => by norm_num) e he] at hd
    exact lt_of_land_high (Nat.mod_lt _ (by positivity)) hd.symm
  refine ⟨fun e => t e + 140737488355328 - 16777216, ?_, fun d hd => ?_⟩
  · have e1 : x + Q = T + BIAS := by omega
    have e2 : encN (fun d => t d + 140737488355328) D =
        encN (fun e => t e + 140737488355328 - 16777216) D + encN (fun _ => 16777216) D := by
      rw [encN_add]
      exact encN_congr fun d _ => by omega
    rw [hTt, hB, encN_add, e2, ← hQ] at e1
    omega
  · have := ht25 d hd
    norm_num at this
    dsimp only
    omega

section Words

variable {G : Type*} [Group G] (gen : ℕ → G)

private theorem commute_bv {z : G} (hz : ∀ c, Commute (LceP.lv gen c) z) (W : ℕ) :
    ∀ n, Commute (LceP.bv gen W n) z
  | 0 => Commute.one_left z
  | n + 1 => by
    rw [LceP.bv_succ]
    exact (commute_bv hz W n).mul_left (hz _)

private theorem bv_rot_central {r n s : ℕ} (hr : r < 256 ^ n) (hs : s < n)
    (hz : ∀ c, Commute (LceP.lv gen c) (LceP.bv gen r n)) :
    LceP.bv gen (rot r n s) n = LceP.bv gen r n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = s + d := ⟨n - s, by omega⟩
  rw [LceP.rot_eq hr (by omega), Nat.add_sub_cancel_left]
  have hA : r / 256 ^ s < 256 ^ d := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm d s]
    exact hr
  have hB : r % 256 ^ s < 256 ^ s := Nat.mod_lt _ (by positivity)
  have hr' : r = r % 256 ^ s + r / 256 ^ s * 256 ^ s := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div r _).symm
  have hval : LceP.bv gen r (s + d) =
      LceP.bv gen (r % 256 ^ s) s * LceP.bv gen (r / 256 ^ s) d := by
    conv_lhs => rw [hr']
    exact LceP.bv_concat gen hB
  have hL : LceP.bv gen (r / 256 ^ s + r % 256 ^ s * 256 ^ d) (s + d) =
      LceP.bv gen (r / 256 ^ s) d * LceP.bv gen (r % 256 ^ s) s := by
    rw [Nat.add_comm s d]
    exact LceP.bv_concat gen hA
  have hc : Commute (LceP.bv gen (r % 256 ^ s) s) (LceP.bv gen r (s + d)) := commute_bv gen hz _ _
  rw [hL]
  set a := LceP.bv gen (r % 256 ^ s) s
  set b := LceP.bv gen (r / 256 ^ s) d
  set z := LceP.bv gen r (s + d)
  calc b * a = a⁻¹ * (a * b) * a := by group
    _ = a⁻¹ * z * a := by rw [← hval]
    _ = z := by rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem wRel_central {INV INV8 W n r m : ℕ} (h : wRel INV INV8 W n r m = true) (hfr : freeRed INV8 W n ≠ 0) (hr : r < 2 ^ (8 * m))
    (hz : ∀ c, Commute (LceP.lv gen c) (LceP.bv gen r m)) :
    LceP.bv gen W n = LceP.bv gen r m := by
  unfold wRel at h
  simp only [LceP.andB_iff, LceP.orB_iff, Nat.beq_eq] at h
  obtain ⟨-, -, hfr' | hrot⟩ := h
  · exact absurd hfr' hfr
  · unfold isRelRot at hrot
    change andB (Nat.beq (strip W n).2 m) (isRot r m (strip W n).1) = true at hrot
    simp only [LceP.andB_iff, Nat.beq_eq] at hrot
    obtain ⟨hk, hrot⟩ := hrot
    obtain ⟨s, hs, hseq⟩ := LceP.anyRec_iff _ m hrot
    rw [Nat.beq_eq] at hseq
    rw [← (LceP.strip_spec gen W n).2, hk, ← hseq]
    rw [LceP.two_pow_eight_mul] at hr
    exact bv_rot_central gen hr hs hz

end Words

private noncomputable def jList (WT : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, J => J :: jList WT k (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight J (nat_lit 1))
      (Nat.shiftRight J (jLen J (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))

private noncomputable def widOf (J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

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

private noncomputable def labRec (WT LB TG : ℕ → ℕ) (BIAS Q HIGH TOP : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.Loop.strictN (labStep LB TG BIAS Q HIGH TOP J S (nat_lit 0) (nat_lit 0))
        (ih (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun wid =>
        CFSG.KC.Loop.strictN (WT wid) (fun w =>
          CFSG.KC.Loop.strictN (labStep LB TG BIAS Q HIGH TOP J S wid w)
            (ih (Nat.shiftRight J (jLen J w))))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem labRec_eq (WT LB TG : ℕ → ℕ) (BIAS Q HIGH TOP : ℕ) : ∀ k J S,
    labRec WT LB TG BIAS Q HIGH TOP k J S =
      (jList WT k J).foldl
        (fun S J => labStep LB TG BIAS Q HIGH TOP J S (widOf J) (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (labStep LB TG BIAS Q HIGH TOP J S (nat_lit 0) (nat_lit 0))
        (labRec WT LB TG BIAS Q HIGH TOP k (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun wid =>
        CFSG.KC.Loop.strictN (WT wid) (fun w =>
          CFSG.KC.Loop.strictN (labStep LB TG BIAS Q HIGH TOP J S wid w)
            (labRec WT LB TG BIAS Q HIGH TOP k (Nat.shiftRight J (jLen J w))))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, widOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;>
      exact labRec_eq WT LB TG BIAS Q HIGH TOP k _ _

private theorem runLab_eq (WT LB TG : ℕ → ℕ) (BIAS Q HIGH TOP : ℕ) : ∀ Cs S,
    runLabZ WT LB TG BIAS Q HIGH TOP Cs S =
      (jAll WT Cs).foldl (fun S J => labStep LB TG BIAS Q HIGH TOP J S (widOf J) (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (labRec WT LB TG BIAS Q HIGH TOP (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runLabZ WT LB TG BIAS Q HIGH TOP Cs) = _
    rw [LceP.strictN_eq, runLab_eq WT LB TG BIAS Q HIGH TOP Cs, labRec_eq]
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

variable {G : Type*} [Group G] (gen g : ℕ → G) (hg : ∀ i j, Commute (g i) (g j)) (D : ℕ)

private def LabHolds (rep : ℕ → G) (R S : ℕ) : Prop :=
  ∃ c, Lab D S c 1 ∧ LceP.el gen rep R = zprod g D (vec c)

private def LRefs (blk LB : ℕ → ℕ) (INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, recOK INV nC (fct blk h) = true ∧ LabHolds gen g D rep (fct blk h) (LB h)

private def WX (rep : ℕ → G) (s W ft : ℕ) (u : G) (lam : ℕ → ℕ) (p cur : ℕ) (c : ℕ → ℕ) : Prop :=
  (p ≤ ft ∧ zprod g D (vec c) = rep s * LceP.bv gen W p * (rep cur)⁻¹) ∨
    (ft < p ∧ ∃ a b : ℕ → ℤ, (∀ d < D, vec c d = a d + vec lam d + b d) ∧
      zprod g D a * u * zprod g D b = rep s * LceP.bv gen W p * (rep cur)⁻¹)

private def WL (rep : ℕ → G) (s W ft : ℕ) (u : G) (lam : ℕ → ℕ) (p st acc : ℕ) : Prop :=
  st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧
    ∃ c, Lab D acc c p ∧ WX gen g D rep s W ft u lam p cur c

private theorem WL_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (lam : ℕ → ℕ) {BIAS : ℕ}
    (hB : BIAS = encN (fun _ => 140737488355328) D) (hs : s < 1048576) :
    WL gen g D rep s W ft u lam 0 (wStart s W) BIAS := by
  right
  refine ⟨s, hs, ?_, _, lab_bias hB 0, Or.inl ⟨Nat.zero_le _, ?_⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [vec_const, zprod_zero, LceP.bv_zero, mul_one, mul_inv_cancel]

include hg in
private theorem WX_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {lam : ℕ → ℕ} {p cur cur' : ℕ}
    {c c'' : ℕ → ℕ} {w : ℕ → ℤ} (hp : p ≠ ft) (hw : ∀ d < D, vec c'' d = vec c d + w d)
    (hy : zprod g D w = rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹)
    (hX : WX gen g D rep s W ft u lam p cur c) : WX gen g D rep s W ft u lam (p + 1) cur' c'' := by
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  rcases hX with ⟨hp', ha⟩ | ⟨hp', a, b, hab, habz⟩
  · refine Or.inl ⟨by omega, ?_⟩
    rw [zprod_congr (b := vec c + w) (fun d hd => by rw [hw d hd, Pi.add_apply]), zprod_add hg, ha,
      hy, e]
  · refine Or.inr ⟨by omega, a, b + w, fun d hd => ?_, ?_⟩
    · rw [hw d hd, hab d hd, Pi.add_apply]
      ring
    · rw [zprod_add hg, ← mul_assoc, habz, hy, e]

include hg in
private theorem WL_ref {blk LB : ℕ → ℕ} {INV INV8 L nC i BIAS : ℕ} (hinv : invOK INV INV8 L = true)
    (hB : BIAS = encN (fun _ => 140737488355328) D)
    {rep : ℕ → G} {s W ft : ℕ} {u : G} {lam : ℕ → ℕ} {p st acc : ℕ} (hpn : p < 4095)
    (e : ℕ) (hrefs : LRefs gen g D blk LB INV nC rep i) (hp : p ≠ ft)
    (hI : WL gen g D rep s W ft u lam p st acc) :
    WL gen g D rep s W ft u lam (p + 1) (refStep blk i e st) (refLab LB BIAS e acc) := by
  unfold refStep refLab
  simp only [LceP.brec_eq, LceP.strictN_eq]
  split_ifs with hh hd
  · rw [Nat.blt_eq] at hh
    obtain ⟨hrec, c', hc'lab, hel⟩ := hrefs _ hh
    set R := fct blk (Nat.shiftRight e (nat_lit 1))
    have hlv := (LceP.lv_fic gen blk hinv hrec).1
    rcases hI with hdead | ⟨cur, hcur, hst, c, hc, hX⟩
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
        obtain ⟨hcR, hw, hs⟩ := bwd_arith hcur hst hm (LceP.fic_lt blk _)
        obtain ⟨hlab, hvec⟩ := lab_addB hc hc'lab (by omega) hB
        refine ⟨fx R, LceP.fx_lt R, by rw [h1, hs], _, hlab, ?_⟩
        refine WX_ext gen g hg D (w := -vec c') hp (fun d hd => by rw [hvec d hd, Pi.neg_apply]; ring)
          ?_ hX
        have hlv' : LceP.lv gen (fic R) = (LceP.lv gen (fc R))⁻¹ := hlv
        rw [zprod_neg hg, ← hel, hw, hlv', hcR]
        unfold LceP.el
        group
  · rw [Nat.blt_eq] at hh
    obtain ⟨hrec, c', hc'lab, hel⟩ := hrefs _ hh
    set R := fct blk (Nat.shiftRight e (nat_lit 1))
    rcases hI with hdead | ⟨cur, hcur, hst, c, hc, hX⟩
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
        obtain ⟨hcR, hw, hs⟩ := fwd_arith hcur hst hm
        obtain ⟨hlab, hvec⟩ := lab_addF hc hc'lab (by omega) hB
        refine ⟨fy R, LceP.fy_lt R, by rw [h1, hs], _, hlab, ?_⟩
        refine WX_ext gen g hg D (w := vec c') hp hvec ?_ hX
        rw [← hel, hw, hcR]
        rfl
  · left
    rfl
  · left
    rfl

private theorem WL_own {rep : ℕ → G} {s W ft Ri Li p st acc BIAS : ℕ} {lam : ℕ → ℕ}
    (hB : BIAS = encN (fun _ => 140737488355328) D) (hp : p = ft) (hpn : p < 4095)
    (hLi : Lab D Li lam 1) (hI : WL gen g D rep s W ft (LceP.el gen rep Ri) lam p st acc) :
    WL gen g D rep s W ft (LceP.el gen rep Ri) lam (p + 1) (sF Ri st) (addF BIAS acc Li) := by
  rcases hI with hdead | ⟨cur, hcur, hst, c, hc, hX⟩
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
      obtain ⟨hcR, hw, hs⟩ := fwd_arith hcur hst hm
      obtain ⟨hlab, hvec⟩ := lab_addF hc hLi (by omega) hB
      refine ⟨fy Ri, LceP.fy_lt Ri, by rw [h1, hs], _, hlab, Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, ha⟩ | ⟨hlt, -⟩
      · refine ⟨vec c, 0, fun d hd => by rw [hvec d hd, Pi.zero_apply, add_zero], ?_⟩
        rw [zprod_zero, mul_one, ha, LceP.bv_succ, hw, hcR]
        unfold LceP.el
        group
      · omega

include hg in
private theorem walk_lab {blk LB : ℕ → ℕ} {INV INV8 L nC i BIAS : ℕ} (hinv : invOK INV INV8 L = true)
    (hB : BIAS = encN (fun _ => 140737488355328) D)
    {rep : ℕ → G} {s W Ri Li ft n : ℕ} {lam : ℕ → ℕ} (hn : n < 1024)
    (hrefs : LRefs gen g D blk LB INV nC rep i) (hLi : Lab D Li lam 1) :
    ∀ k ≤ n, ∀ J st acc,
      WL gen g D rep s W ft (LceP.el gen rep Ri) lam (n - k) st acc →
      WL gen g D rep s W ft (LceP.el gen rep Ri) lam n
        (walkGo blk i Ri ft n k J st) (labGo LB BIAS Li ft n k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen g D rep s W ft (LceP.el gen rep Ri) lam n
      (Bool.rec (motive := fun _ => ℕ)
        (walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st))
        (walkGo blk i Ri ft n k J (sF Ri st)) (Nat.beq (Nat.sub n (Nat.succ k)) ft))
      (Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.Loop.strictN (refLab LB BIAS (Nat.land J 4294967295) acc)
          (labGo LB BIAS Li ft n k (Nat.shiftRight J 32)))
        (CFSG.KC.Loop.strictN (addF BIAS acc Li) (labGo LB BIAS Li ft n k J))
        (Nat.beq (Nat.sub n (Nat.succ k)) ft))
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hB hn hrefs hLi k (by omega)
      rw [e]
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      exact WL_ref gen g hg D hinv hB (by omega) _ hrefs hp hI
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hB hn hrefs hLi k (by omega)
      rw [e]
      exact WL_own gen g D hB (Nat.eq_of_beq_eq_true hb) (by omega) hLi hI

include hg in
private theorem walk_cyc {blk LB : ℕ → ℕ} {INV INV8 L nC i BIAS : ℕ} (hinv : invOK INV INV8 L = true)
    (hB : BIAS = encN (fun _ => 140737488355328) D)
    {rep : ℕ → G} {s W n : ℕ} {u : G} {lam : ℕ → ℕ} (hn : n < 1024)
    (hrefs : LRefs gen g D blk LB INV nC rep i) :
    ∀ k ≤ n, ∀ J st acc, WL gen g D rep s W n u lam (n - k) st acc →
      WL gen g D rep s W n u lam n (CFSG.KC.HSK.cycWalk blk i k J st) (cycLab LB BIAS k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen g D rep s W n u lam n
      (CFSG.KC.Loop.strictN (refStep blk i (Nat.land J 4294967295) st)
        (CFSG.KC.HSK.cycWalk blk i k (Nat.shiftRight J 32)))
      (CFSG.KC.Loop.strictN (refLab LB BIAS (Nat.land J 4294967295) acc)
        (cycLab LB BIAS k (Nat.shiftRight J 32)))
    rw [LceP.strictN_eq, LceP.strictN_eq]
    apply walk_cyc hinv hB hn hrefs k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_ref gen g hg D hinv hB (by omega) _ hrefs (by omega) hI

private def LInv (nR : ℕ) (blk LB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ (∀ k < N, ∀ r < nR, Commute (rep k) (g r)) ∧
    ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) → (∀ k, ∀ r < nR, Commute (rep' k) (g r)) →
      LRefs gen g D blk LB INV nC rep' i

private def LGood (nR : ℕ) (blk LB : ℕ → ℕ) (INV nC S T I : ℕ) : Prop :=
  S = 0 ∨ T = 0 ∨ I = 0 ∨ 4294967296 < T ∨
    (1 ≤ sN S ∧ T = sI S + 1 ∧ LInv gen g D nR blk LB INV nC (sI S) (sN S))

private theorem target_spec {RT ST : ℕ → ℕ} {INV INV8 L nR K BIAS : ℕ} (hinv : invOK INV INV8 L = true)
    (hRT : ∀ r < nR, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧
      LceP.bv gen (wWord (RT r)) (wLen (RT r)) = g r ∧ ∀ c, Commute (LceP.lv gen c) (g r))
    (hST : ∀ j < K, LceP.bv gen (wWord (ST j)) (wLen (ST j)) = g (nR + j))
    (hB : BIAS = encN (fun _ => 140737488355328) D) (hnRK : nR + K ≤ D)
    {w h t : ℕ} (htg : tgOne INV8 nR K BIAS w h t = true)
    (hw2 : wKind w = 2 → wRel INV INV8 (wWord w) (wLen w) (wWord (RT h)) (wLen (RT h)) = true)
    (hw3 : wKind w = 3 → wSub INV (wWord w) (wLen w) (wWord (ST h)) (wLen (ST h)) = true) :
    (wKind w = 2 → ∃ ct, Lab D t ct 1 ∧ ∀ x : G, (∀ r < nR, Commute x (g r)) →
      x * LceP.bv gen (wWord w) (wLen w) * x⁻¹ = zprod g D (vec ct)) ∧
    (wKind w = 3 → ∃ ct, Lab D t ct 1 ∧ LceP.bv gen (wWord w) (wLen w) = zprod g D (vec ct)) := by
  unfold tgOne at htg
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h3 : Nat.beq (wKind w) (nat_lit 3) = false := by rw [hk]; rfl
    have h2 : Nat.beq (wKind w) (nat_lit 2) = true := by rw [hk]; rfl
    rw [h3, h2] at htg
    have hrel := hw2 hk
    cases hfr : Nat.beq (freeRed INV8 (wWord w) (wLen w)) (nat_lit 0)
    · rw [hfr] at htg
      simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at htg
      obtain ⟨hh, ht⟩ := htg
      have hfr' : freeRed INV8 (wWord w) (wLen w) ≠ 0 := by
        intro h0
        rw [h0] at hfr
        exact absurd hfr (by decide)
      obtain ⟨hcl, hval, hcom⟩ := hRT h hh
      have hbv := wRel_central gen hrel hfr' hcl (by rw [hval]; exact hcom)
      have ht' : t = BIAS + 2 ^ (48 * h) := by
        rw [ht]
        change BIAS + 1 <<< (48 * h) = _
        rw [Nat.shiftLeft_eq, one_mul]
      refine ⟨_, ht' ▸ lab_single hB (by omega), fun x hx => ?_⟩
      rw [zprod_single (by omega), hbv, hval, (hx h hh).eq, mul_assoc, mul_inv_cancel, mul_one]
    · rw [hfr] at htg
      have ht : t = BIAS := Nat.eq_of_beq_eq_true htg
      have hfr0 : freeRed INV8 (wWord w) (wLen w) = 0 := Nat.eq_of_beq_eq_true hfr
      have hlet : lettersOK INV (wWord w) (wLen w) = true := by
        unfold wRel at hrel
        exact ((LceP.andB_iff _ _).1 hrel).1
      have hbv := LceP.freeRed_zero gen hinv hlet hfr0
      refine ⟨_, ht ▸ lab_bias hB 1, fun x _ => ?_⟩
      rw [vec_const, zprod_zero, hbv, mul_one, mul_inv_cancel]
  · have h3 : Nat.beq (wKind w) (nat_lit 3) = true := by rw [hk]; rfl
    rw [h3] at htg
    simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at htg
    obtain ⟨hh, ht⟩ := htg
    have ht' : t = BIAS + 2 ^ (48 * (nR + h)) := by
      rw [ht]
      change BIAS + 1 <<< (48 * (nR + h)) = _
      rw [Nat.shiftLeft_eq, one_mul]
    refine ⟨_, ht' ▸ lab_single hB (by omega), ?_⟩
    rw [zprod_single (by omega), LceP.wSub_sound gen (hw3 hk), hST h hh]

private theorem labStep_cases (LB TG : ℕ → ℕ) (BIAS Q HIGH TOP J T wid w : ℕ) :
    labStep LB TG BIAS Q HIGH TOP J T wid w = 0 ∨ labStep LB TG BIAS Q HIGH TOP J T wid w = T + 1 := by
  unfold labStep
  cases Nat.blt (nat_lit 0) T
  · exact Or.inl rfl
  · dsimp only
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> dsimp only
    · cases Nat.beq (LB (Nat.sub T (nat_lit 1))) BIAS
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases labWalk LB TG BIAS Q HIGH TOP (Nat.sub T (nat_lit 1)) J wid w
      · exact Or.inl rfl
      · exact Or.inr rfl

include hg in
private theorem LGood_step {blk WT LB TG : ℕ → ℕ} {INV INV8 L nC m nR BIAS Q HIGH TOP : ℕ}
    (hinv : invOK INV INV8 L = true) (hB : BIAS = encN (fun _ => 140737488355328) D)
    (hconst : constsOK D BIAS Q HIGH TOP = true)
    (hlc : ∀ r < nR, ∀ c, Commute (LceP.lv gen c) (g r))
    (htg : ∀ id < m, (wKind (WT id) = 2 → ∃ ct, Lab D (TG id) ct 1 ∧ ∀ x : G,
        (∀ r < nR, Commute x (g r)) →
          x * LceP.bv gen (wWord (WT id)) (wLen (WT id)) * x⁻¹ = zprod g D (vec ct)) ∧
      (wKind (WT id) = 3 → ∃ ct, Lab D (TG id) ct 1 ∧
        LceP.bv gen (wWord (WT id)) (wLen (WT id)) = zprod g D (vec ct)))
    {S T I : ℕ} (J : ℕ) (hG : LGood gen g D nR blk LB INV nC S T I) :
    LGood gen g D nR blk LB INV nC (factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J))
      (labStep LB TG BIAS Q HIGH TOP J T (widOf J) (wOf WT J)) (idsF m I J) := by
  rcases hG with h0 | h0 | h0 | h0 | ⟨hN, hT, rep, hrep0, hcomm, hrefs⟩
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
  · rcases labStep_cases LB TG BIAS Q HIGH TOP J T (widOf J) (wOf WT J) with h | h
    · right; left
      exact h
    · right; right; right; left
      rw [h]
      omega
  set i := sI S with hidef
  set N := sN S with hNdef
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
  have hnext : ∀ N' : ℕ, 1 ≤ N' → LInv gen g D nR blk LB INV nC (i + 1) N' → ∀ I' : ℕ,
      LGood gen g D nR blk LB INV nC (mkS (Nat.succ i) N') (T + 1) I' := by
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
  unfold factStep labStep idsF wOf widOf
  rw [hS0, hT0, hT1]
  dsimp only
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases hft : fTree INV nC L (fct blk i) N
    · left
      rfl
    cases hlb : Nat.beq (LB i) BIAS
    · right; left
      rfl
    dsimp only
    refine hnext (N + 1) (by omega) ?_ _
    unfold fTree at hft
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at hft
    obtain ⟨hrR, hfy, hfx, -⟩ := hft
    have hLB : LB i = BIAS := Nat.eq_of_beq_eq_true hlb
    set R := fct blk i
    refine ⟨Function.update rep N (rep (fx R) * LceP.lv gen (fc R)), ?_, ?_,
      fun rep' hag hc' h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    · intro k hk r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [Function.update_of_ne (show k ≠ N by omega)]
        exact hcomm k hk r hr
      · rw [Function.update_self]
        exact (hcomm _ hfx r hr).mul_left (hlc r hr _)
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' hc' h hh
    · refine ⟨hrR, _, hLB ▸ lab_bias hB 1, ?_⟩
      rw [vec_const, zprod_zero]
      unfold LceP.el
      rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel]
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
    cases hlw : labWalk LB TG BIAS Q HIGH TOP i J id w
    · right; left
      rfl
    dsimp only
    set R := fct blk i
    refine hnext N hN ⟨rep, hrep0, hcomm, fun rep' hag hc' h hh => ?_⟩ _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag hc' h hh
    unfold walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hwalk⟩ := hwk
    unfold labWalk at hlw
    rw [LceP.letB_eq] at hlw
    simp only [LceP.andB_iff, Nat.beq_eq] at hlw
    obtain ⟨hval, hlab⟩ := hlw
    obtain ⟨lam, hlam⟩ := valid_lab hconst hval
    have hn : wLen w < 1024 := by
      change Nat.land (Nat.shiftRight w 2) 1023 < 1024
      rw [LceP.land_lit _ 10 1023 (by norm_num)]
      exact Nat.mod_lt _ (by norm_num)
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag hc'
    have hstart := WL_start gen g D rep' (wWord w) ft (LceP.el gen rep' R) lam hB hfs
    have hW := walk_lab gen g hg D hinv hB hn hrefs' hlam (wLen w) le_rfl (Nat.shiftRight J 53) _ _
      (by rw [Nat.sub_self]; exact hstart)
    rw [hwalk, hlab] at hW
    refine ⟨hrec, ?_⟩
    rcases hW with hdead | ⟨cur, hcur, hst, c, hc, hX⟩
    · exfalso
      omega
    have hc0 : cur = fs := by omega
    rcases hX with ⟨hle, -⟩ | ⟨-, a, b, hab, habz⟩
    · exfalso
      omega
    rw [hc0] at habz
    have hval : ∃ ct, Lab D (TG id) ct 1 ∧
        rep' fs * LceP.bv gen (wWord w) (wLen w) * (rep' fs)⁻¹ = zprod g D (vec ct) := by
      rcases hkind with hk2 | ⟨hk3, hfs0⟩
      · obtain ⟨ct, hct, hx⟩ := (htg id hidm).1 hk2
        exact ⟨ct, hct, hx _ fun r hr => hc' fs r hr⟩
      · obtain ⟨ct, hct, hbv⟩ := (htg id hidm).2 hk3
        have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
        refine ⟨ct, hct, ?_⟩
        rw [hfs0, h0, one_mul, inv_one, mul_one, hbv]
    obtain ⟨ct, hct, hv⟩ := hval
    have hsum : zprod g D (vec ct) = zprod g D a * zprod g D (vec lam) * zprod g D b := by
      rw [← zprod_add hg, ← zprod_add hg]
      exact zprod_congr fun d hd => by
        rw [lab_unique hct hc (by norm_num) (by omega) d hd, hab d hd, Pi.add_apply, Pi.add_apply]
    rw [hv, hsum] at habz
    exact ⟨lam, hlam, mul_left_cancel (mul_right_cancel habz)⟩

end Lab

theorem cyc_sound {G : Type*} [Group G] (gen g : ℕ → G) (hcomm : ∀ i j, Commute (g i) (g j))
    {blk WT RT ST LB TG : ℕ → ℕ}
    {INV INV8 L nC nf m Hs K nR D BIAS Q HIGH TOP S0 S1 T0 T1 : ℕ} {Cs : List ℕ}
    (h : coneOk blk WT RT ST LB TG INV INV8 L nC nf m Hs K nR D BIAS Q HIGH TOP S0 S1 T0 T1 Cs
      = true)
    (hRT : ∀ r < nR, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧
      bval gen (wWord (RT r)) (wLen (RT r)) = g r ∧ ∀ c, Commute (letV gen c) (g r))
    (hST : ∀ j < K, bval gen (wWord (ST j)) (wLen (ST j)) = g (nR + j))
    {nf' c wid R V : ℕ} (hnf : nf' = nf) (hc : c < 2 ^ 20) (hwid : wid < m)
    (hcyc : cycZ blk WT LB BIAS nf' c wid R V = true) :
    zprod g D (decZ V) = zprod g D (decZ (TG wid)) := by
  subst nf'
  unfold coneOk at h
  obtain ⟨hwords, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hconst, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨htgok, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hrun, hlab⟩ := (LceP.andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := LceP.blt_true hnf
  have hB : BIAS = encN (fun _ => 140737488355328) D := by
    have hc2 := hconst
    unfold constsOK at hc2
    simp only [LceP.andB_iff, Nat.beq_eq] at hc2
    rw [hc2.2.1, lanes_eq]
  have hRT' : ∀ r < nR, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧
      LceP.bv gen (wWord (RT r)) (wLen (RT r)) = g r ∧ ∀ c, Commute (LceP.lv gen c) (g r) := hRT
  have hST' : ∀ j < K, LceP.bv gen (wWord (ST j)) (wLen (ST j)) = g (nR + j) := hST
  have hlc : ∀ r < nR, ∀ c, Commute (LceP.lv gen c) (g r) := fun r hr => (hRT' r hr).2.2
  have hw : ∀ j < m,
      (wKind (WT j) = 2 → wRel INV INV8 (wWord (WT j)) (wLen (WT j))
        (wWord (RT (CFSG.KC.HSK.hint Hs j))) (wLen (RT (CFSG.KC.HSK.hint Hs j))) = true) ∧
      (wKind (WT j) = 3 → wSub INV (wWord (WT j)) (wLen (WT j))
        (wWord (ST (CFSG.KC.HSK.hint Hs j))) (wLen (ST (CFSG.KC.HSK.hint Hs j))) = true) := by
    intro j hj
    have hl := LceP.hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords j hj
    rw [Nat.sub_self, Nat.zero_add] at hl
    exact LceP.word_check hl
  unfold tgOK at htgok
  obtain ⟨hnRK, htgs⟩ := (LceP.andB_iff _ _).1 htgok
  have hnRK' : nR + K ≤ D := by
    rw [Nat.ble_eq] at hnRK
    exact hnRK
  have htg1 := (LceP.allRec_iff (fun k => tgOne INV8 nR K BIAS (WT k) (CFSG.KC.HSK.hint Hs k) (TG k))
    m).1 htgs
  have htg := fun id (hid : id < m) => target_spec gen g D hinv hRT' hST' hB hnRK' (htg1 id hid)
    (hw id hid).1 (hw id hid).2
  have hstep := fun (J : ℕ) {S T I : ℕ} => LGood_step gen g hcomm D (blk := blk) (WT := WT)
    (LB := LB) (TG := TG) (L := L) (nC := nC) (m := m) (nR := nR)
    (S := S) (T := T) (I := I) hinv hB hconst hlc htg J
  have hfold : ∀ (l : List ℕ) (S T I : ℕ), LGood gen g D nR blk LB INV nC S T I →
      LGood gen g D nR blk LB INV nC
        (l.foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S)
        (l.foldl (fun S J => labStep LB TG BIAS Q HIGH TOP J S (widOf J) (wOf WT J)) T)
        (l.foldl (idsF m) I) := by
    intro l
    induction l with
    | nil => intro S T I hG; exact hG
    | cons J l ih =>
      intro S T I hG
      simp only [List.foldl_cons]
      exact ih _ _ _ (hstep J hG)
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hT0' : T0 = 1 := Nat.eq_of_beq_eq_true hT0
  have hG0 : LGood gen g D nR blk LB INV nC S0 T0 1 := by
    right; right; right; right
    have e1 : sI S0 = 0 := by rw [hS0', LceP.sI_eq, LceP.mkS_eq 1 (by norm_num)]
    have e2 : sN S0 = 1 := by rw [hS0', LceP.sN_eq, LceP.mkS_eq 1 (by norm_num)]
    rw [e1, e2, hT0']
    refine ⟨le_rfl, rfl, fun _ => 1, rfl, fun _ _ _ _ => Commute.one_left _,
      fun _ _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := hfold (jAll WT Cs) S0 T0 1 hG0
  rw [← runFacts_eq, ← runLab_eq, ← runIds_eq, Nat.eq_of_beq_eq_true hrun,
    Nat.eq_of_beq_eq_true hlab, Nat.eq_of_beq_eq_true hids, Nat.eq_of_beq_eq_true hS1,
    Nat.eq_of_beq_eq_true hT1] at hG1
  have hL : ∃ rep : ℕ → G, (∀ k, ∀ r < nR, Commute (rep k) (g r)) ∧
      LRefs gen g D blk LB INV nC rep nf := by
    rcases hG1 with h0 | h0 | h0 | h0 | ⟨-, -, rep, -, hcm, hrefs⟩
    · rw [LceP.mkS_eq nC hnf'] at h0
      have h0' : nf = 0 := by omega
      exact ⟨fun _ => 1, fun _ _ _ => Commute.one_left _, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (Nat.succ_ne_zero nf)
    · exact absurd h0 one_ne_zero
    · exfalso
      change 4294967296 < nf + 1 at h0
      omega
    · have e1 : sI (mkS nf nC) = nf := by
        rw [LceP.sI_eq, LceP.mkS_eq nC hnf']
        omega
      have hcm' : ∀ k, ∀ r < nR,
          Commute ((fun k => if k < sN (mkS nf nC) then rep k else 1) k) (g r) := by
        intro k r hr
        dsimp only
        split_ifs with hk
        · exact hcm k hk r hr
        · exact Commute.one_left _
      refine ⟨_, hcm', ?_⟩
      have hr := hrefs _ (fun k hk => by simp only [hk, ↓reduceIte]) hcm'
      rwa [e1] at hr
  obtain ⟨rep, hcm, hrefs⟩ := hL
  unfold cycZ at hcyc
  rw [LceP.letB_eq] at hcyc
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.add_eq] at hcyc
  obtain ⟨hk2, hwalk, hlab'⟩ := hcyc
  have hc' : c < 1048576 := by simpa using hc
  have hn : wLen (WT wid) < 1024 := by
    change Nat.land (Nat.shiftRight (WT wid) 2) 1023 < 1024
    rw [LceP.land_lit _ 10 1023 (by norm_num)]
    exact Nat.mod_lt _ (by norm_num)
  have hstart := WL_start gen g D rep (wWord (WT wid)) (wLen (WT wid)) 1 (fun _ => 0) hB hc'
  have hW := walk_cyc gen g hcomm D hinv hB hn hrefs (wLen (WT wid)) le_rfl R _ _
    (by rw [Nat.sub_self]; exact hstart)
  rw [hwalk, hlab'] at hW
  rcases hW with hdead | ⟨cur, hcur, hst, cv, hcv, hX⟩
  · exfalso
    omega
  have hc0 : cur = c := by omega
  rcases hX with ⟨-, hz⟩ | ⟨hlt, -⟩
  · obtain ⟨ct, hct, hx⟩ := (htg wid hwid).1 hk2
    rw [hc0, hx _ (hcm c)] at hz
    calc zprod g D (decZ V) = zprod g D (vec cv) :=
          zprod_congr fun d hd => decZ_lab hcv (by omega) hd
      _ = zprod g D (vec ct) := hz
      _ = zprod g D (decZ (TG wid)) :=
          (zprod_congr fun d hd => decZ_lab hct (by norm_num) hd).symm
  · exact absurd hlt (lt_irrefl _)

end CFSG.Certificates.LabZ

end
