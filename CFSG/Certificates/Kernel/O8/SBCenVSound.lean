module

public import Certificates.Data.Kernel.O8.SBCenV
public import CFSG.Certificates.Kernel.O8.SBCenUSound

public section

namespace CFSG.KC.SBCenV

open CFSG.KC.Enum CFSG.KC.SB CFSG.KC.SBCen CFSG.KC.SBCenL CFSG.KC.SBCenU CFSG.KC.AxisPlane
  CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def linC (R x : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => linC R x i ^^^ ((x >>> i) &&& 1) * ((R >>> (7 * (1 <<< i))) &&& 127)

theorem ln_zero (s : ℕ) : ((0 : ℕ) >>> s) &&& 127 = 0 := by
  rw [Nat.zero_shiftRight, Nat.zero_and]

theorem bit_le (x i : ℕ) : (x >>> i) &&& 1 ≤ 1 := Nat.and_le_right

theorem ln_bitmul {X i b e : ℕ} (hi : i < 7) (hb : b < 128) (he : e < 128) :
    ((((X >>> i) &&& RU) * b) >>> (7 * e)) &&& 127 = ((((X >>> (7 * e)) &&& 127) >>> i) &&& 1) * b := by
  have hL : (X >>> i) &&& RU = lanes 7 (fun e => (((X >>> (7 * e)) &&& 127) >>> i) &&& 1) 128 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_shiftRight, RU, lanesK_eq, tb_lanes (fun _ _ => by norm_num),
      tb_lanes (fun _ _ => Nat.lt_of_le_of_lt (bit_le _ _) (by norm_num)), tb1, Nat.testBit_and,
      Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_shiftRight, tb127, tb1]
    by_cases h0 : j % 7 = 0
    · have e1 : 7 * (j / 7) + (i + j % 7) = i + j := by omega
      rw [e1, h0, decide_eq_true (by omega : i + 0 < 7), decide_eq_true (by omega : (0 : ℕ) < 1)]
      cases X.testBit (i + j) <;> cases decide (j < 7 * 128) <;> rfl
    · rw [decide_eq_false (by omega : ¬ j % 7 < 1)]
      simp
  rw [hL, Nat.mul_comm (lanes _ _ _) b, lanes_cmul,
    ln_lanes (fun e _ => Nat.lt_of_le_of_lt (Nat.mul_le_mul_left b (bit_le _ _)) (by omega)) he,
    Nat.mul_comm]

theorem ln_linLn (R X : ℕ) {e : ℕ} (he : e < 128) :
    ∀ n, n ≤ 7 → (linLn R X n >>> (7 * e)) &&& 127 = linC R ((X >>> (7 * e)) &&& 127) n
  | 0, _ => ln_zero _
  | n + 1, hn => by
    have ih := ln_linLn R X he n (by omega)
    change ((linLn R X n ^^^ ((X >>> n) &&& RU) * ((R >>> (7 * (1 <<< n))) &&& 127)) >>> (7 * e)) &&& 127 = _
    rw [ln_xor, ih, ln_bitmul (by omega) (ln_lt _ _) he]
    rfl

theorem ln_linL (R X : ℕ) {e : ℕ} (he : e < 128) :
    (linL R X >>> (7 * e)) &&& 127 = linC R ((X >>> (7 * e)) &&& 127) 7 :=
  ln_linLn R X he 7 le_rfl

theorem xor_xor4 (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem bit_xor (x y i : ℕ) : ((x ^^^ y) >>> i) &&& 1 = ((x >>> i) &&& 1) ^^^ ((y >>> i) &&& 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases x.testBit (i + j) <;> cases y.testBit (i + j) <;> simp

theorem linC_xor (R x y : ℕ) : ∀ n, linC R (x ^^^ y) n = linC R x n ^^^ linC R y n
  | 0 => by simp [linC]
  | n + 1 => by
    simp only [linC]
    rw [linC_xor R x y n, bit_xor]
    have ha := bit_le x n
    have hb := bit_le y n
    generalize (x >>> n) &&& 1 = a at ha ⊢
    generalize (y >>> n) &&& 1 = b at hb ⊢
    generalize (R >>> (7 * (1 <<< n))) &&& 127 = B
    rw [xor_xor4]
    congr 1
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
      rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp

theorem act_lin {R : ℕ} (h : linOK R = true) {x : ℕ} (hx : x < 128) :
    (R >>> (7 * x)) &&& 127 = linC R x 7 := by
  have hR : linL R IDX = R := Nat.eq_of_beq_eq_true h
  calc (R >>> (7 * x)) &&& 127 = (linL R IDX >>> (7 * x)) &&& 127 := by rw [hR]
    _ = linC R x 7 := by rw [ln_linL R IDX hx, ln_IDX hx]

theorem act_xor {R : ℕ} (h : linOK R = true) {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    (R >>> (7 * (x ^^^ y))) &&& 127 = ((R >>> (7 * x)) &&& 127) ^^^ ((R >>> (7 * y)) &&& 127) := by
  rw [act_lin h (xor_lt hx hy), act_lin h hx, act_lin h hy, linC_xor]

theorem ln_linL_act {R X : ℕ} (h : linOK R = true) {e : ℕ} (he : e < 128) :
    (linL R X >>> (7 * e)) &&& 127 = (R >>> (7 * ((X >>> (7 * e)) &&& 127))) &&& 127 := by
  rw [ln_linL R X he, act_lin h (ln_lt _ _)]

theorem beq_dec (a b : ℕ) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem flg_or (p q : ℕ → Bool) : flg p ||| flg q = flg fun e => p e || q e := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, tb_flg, tb_flg, tb_flg]
  cases decide (i < 7 * 128) <;> cases decide (i % 7 = 6) <;> cases p (i / 7) <;> cases q (i / 7) <;>
    rfl

theorem fibOf_mask (F : ℕ → ℕ) (w : ℕ) :
    lanesK (fun e => nIf(Nat.beq (Nat.shiftRight (F e) 7) w, 64, 0)) 128 =
      flg fun e => decide (F e >>> 7 = w) := by
  rw [lanesK_eq]
  unfold flg
  refine congrArg (fun f => lanes 7 f 128) (funext fun e => ?_)
  rw [cen_nIf, cen_beq]
  rfl

theorem fibOf_lo (F : ℕ → ℕ) {w : ℕ} (hw : w < 512) : Nat.land (fibOf F w) 511 = w := by
  unfold fibOf
  rw [nl_and, Nat.add_eq, cen_shl, Nat.and_two_pow_sub_one_eq_mod _ 9]
  omega

theorem fibOf_hi (F : ℕ → ℕ) {w : ℕ} (hw : w < 512) :
    Nat.shiftRight (fibOf F w) 9 = flg fun e => decide (F e >>> 7 = w) := by
  unfold fibOf
  rw [nl_shr, Nat.add_eq, cen_shl, Nat.shiftRight_eq_div_pow, fibOf_mask]
  omega

theorem recMap (F : ℕ → ℕ) : ∀ Om : List ℕ,
    List.rec (motive := fun _ => List ℕ) [] (fun w _ ih => List.cons (fibOf F w) ih) Om = Om.map (fibOf F)
  | [] => rfl
  | w :: Om => by
    change fibOf F w :: _ = _
    rw [recMap F Om, List.map_cons]

theorem memN_sound {x : ℕ} : ∀ {L : List ℕ}, memN x L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | w :: L, h => by
    change Bool.rec (motive := fun _ => Bool) (memN x L) true (Nat.beq x w) = true at h
    cases hb : Nat.beq x w
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (memN_sound h)
    · rw [Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

theorem covK_sound {F : ℕ → ℕ} {Om : List ℕ} (h : covK F Om = true) : ∀ e < 128, F e >>> 7 ∈ Om := by
  intro e he
  exact memN_sound (recAnd (P := fun e => memN (Nat.shiftRight (F e) 7) Om) h e he)

section Grp

variable (AR MR : ℕ → ℕ) {mul : ℕ → ℕ → ℕ} (F : ℕ → ℕ) (z : ℕ)
  (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d)
  (hF : ∀ a < 65536, F a < 65536) (hz : z < 65536)
  (hlin : ∀ h < 512, linOK (AR h) = true)

include hmul hlin in
theorem sq_eq {e g f0 w c0 c1 z0 z1 : ℕ} (he : e < 128) (hg : g < 512) (hf0 : f0 < 128) (hw : w < 512)
    (hc0 : c0 < 128) (hc1 : c1 < 512) (hz0 : z0 < 128) (hz1 : z1 < 512)
    (hFm : F (e + 128 * g) = mul (f0 + 128 * w) (c0 + 128 * c1)) (hzz : z = z0 + 128 * z1) :
    mul (mul (e + 128 * g) (F (e + 128 * g))) z =
      ((e ^^^ ((AR g >>> (7 * f0)) &&& 127)) ^^^ (((AR g >>> (7 * ((AR w >>> (7 * c0)) &&& 127))) &&& 127)
        ^^^ ((AR ((MR g >>> (9 * ((MR w >>> (9 * c1)) &&& 511))) &&& 511) >>> (7 * z0)) &&& 127))) +
      128 * ((MR ((MR g >>> (9 * ((MR w >>> (9 * c1)) &&& 511))) &&& 511) >>> (9 * z1)) &&& 511) := by
  rw [hFm, mul_code AR MR hmul hf0 hw hc0 hc1,
    mul_code AR MR hmul he hg (xor_lt hf0 (ln_lt _ _)) (mt_lt _ _ _), hzz,
    mul_code AR MR hmul (xor_lt he (ln_lt _ _)) (mt_lt _ _ _) hz0 hz1, act_xor (hlin g hg) hf0 (ln_lt _ _)] <;>
    simp only [Nat.xor_assoc]

variable {Om : List ℕ} (hOm : ∀ w ∈ Om, w < 512) (hcov : ∀ e < 128, F e >>> 7 ∈ Om)
  (hFm : ∀ e < 128, ∀ g < 512, F (e + 128 * g) = mul (F e) (F (128 * g)))

@[expose] def usq (e g : ℕ) : ℕ := mul (mul (e + 128 * g) (F (e + 128 * g))) z

include hmul hF hz hlin hFm in
theorem usq_fib {e g : ℕ} (he : e < 128) (hg : g < 512) :
    usq F z (mul := mul) e g =
      ((e ^^^ ((linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128) >>> (7 * e)) &&& 127)) ^^^
        (((AR g >>> (7 * ((AR (F e >>> 7) >>> (7 * (F (128 * g) &&& 127))) &&& 127))) &&& 127) ^^^
        ((AR ((MR g >>> (9 * ((MR (F e >>> 7) >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) >>>
          (7 * (z &&& 127))) &&& 127))) +
      128 * ((MR ((MR g >>> (9 * ((MR (F e >>> 7) >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) >>>
        (9 * (z >>> 7))) &&& 511) := by
  obtain ⟨hFs, hF0, hF1⟩ := code_split (hF e (by omega))
  obtain ⟨hcs, hc0, hc1⟩ := code_split (hF (128 * g) (by omega))
  obtain ⟨hzs, hz0, hz1⟩ := code_split hz
  have hP : (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128) >>> (7 * e)) &&& 127 =
      (AR g >>> (7 * (F e &&& 127))) &&& 127 := by
    rw [ln_linL_act (hlin g hg) he, lanesK_eq,
      ln_lanes (f := fun e => Nat.land (F e) 127) (fun _ _ => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)) he]
    rfl
  rw [hP]
  unfold usq
  exact sq_eq AR MR F z hmul hlin he hg hF0 hF1 hc0 hc1 hz0 hz1
    (by rw [hFm e he g hg, ← hFs, ← hcs]) hzs

include hmul hF hz hlin hFm in
theorem fibI_eq {g w : ℕ} (hg : g < 512) (hw : w < 512) :
    fibI AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g)) z
        (fibOf F w) =
      flg fun e => decide (F e >>> 7 = w) && decide (usq F z (mul := mul) e g = 0) := by
  unfold fibI
  simp only [cen_strictN]
  rw [fibOf_lo F hw, fibOf_hi F hw]
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, nl_and, nl_shr, nl_xor, Nat.mul_eq]
  split_ifs with hp
  · rw [zl_eq, flg_and]
    apply flg_congr
    intro e he
    by_cases hwe : F e >>> 7 = w
    · rw [usq_fib AR MR F z hmul hF hz hlin hFm he hg, hwe, hp, ln_xor, ln_xor, ln_IDX he,
        ln_RU (xor_lt (ln_lt _ _) (ln_lt _ _)) he]
      simp only [hwe, decide_true, Bool.true_and, Nat.mul_zero, Nat.add_zero, beq_dec]
      rfl
    · simp [hwe]
  · symm
    apply flg_false
    intro e he
    by_cases hwe : F e >>> 7 = w
    · rw [usq_fib AR MR F z hmul hF hz hlin hFm he hg, hwe]
      simp only [decide_true, Bool.true_and, decide_eq_false_iff_not]
      omega
    · simp [hwe]

include hmul hF hz hlin hFm in
theorem fibO_eq {g w : ℕ} (hg : g < 512) (hw : w < 512) :
    fibO AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g)) z
        (fibOf F w) =
      flg fun e => decide (F e >>> 7 = w) && decide (usq F z (mul := mul) e g ≠ 0 ∧
        mul (usq F z (mul := mul) e g) (usq F z (mul := mul) e g) = 0) := by
  unfold fibO
  simp only [cen_strictN]
  rw [fibOf_lo F hw, fibOf_hi F hw]
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, nl_and, nl_shr, nl_xor, Nat.mul_eq]
  have hp5 := mt_lt MR ((MR g >>> (9 * ((MR w >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) (z >>> 7)
  generalize hpd : (MR ((MR g >>> (9 * ((MR w >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) >>>
    (9 * (z >>> 7))) &&& 511 = p at hp5
  have hsq : ∀ e < 128, F e >>> 7 = w → usq F z (mul := mul) e g =
      ((((IDX ^^^ linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) ^^^
        ((AR g >>> (7 * ((AR w >>> (7 * (F (128 * g) &&& 127))) &&& 127))) &&& 127 ^^^
          (AR ((MR g >>> (9 * ((MR w >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) >>>
            (7 * (z &&& 127))) &&& 127) * RU) >>> (7 * e)) &&& 127) + 128 * p := by
    intro e he hwe
    rw [usq_fib AR MR F z hmul hF hz hlin hFm he hg, hwe, hpd, ln_xor, ln_xor, ln_IDX he,
      ln_RU (xor_lt (ln_lt _ _) (ln_lt _ _)) he]
  generalize ((IDX ^^^ linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) ^^^
        ((AR g >>> (7 * ((AR w >>> (7 * (F (128 * g) &&& 127))) &&& 127))) &&& 127 ^^^
          (AR ((MR g >>> (9 * ((MR w >>> (9 * (F (128 * g) >>> 7))) &&& 511))) &&& 511) >>>
            (7 * (z &&& 127))) &&& 127) * RU) = X at hsq ⊢
  have hss : ∀ e < 128, F e >>> 7 = w → mul (usq F z (mul := mul) e g) (usq F z (mul := mul) e g) =
      (((X >>> (7 * e)) &&& 127) ^^^ ((linL (AR p) X >>> (7 * e)) &&& 127)) +
        128 * ((MR p >>> (9 * p)) &&& 511) := by
    intro e he hwe
    rw [hsq e he hwe, mul_code AR MR hmul (ln_lt _ _) hp5 (ln_lt _ _) hp5, ln_linL_act (hlin p hp5) he]
  split_ifs with h4 hp
  · rw [zl_eq, zl_eq, flg_and, flg_xor, flg_and]
    apply flg_congr
    intro e he
    by_cases hwe : F e >>> 7 = w
    · subst hp
      rw [hss e he hwe, hsq e he hwe, h4, ln_xor]
      simp only [hwe, decide_true, Bool.true_and, Nat.mul_zero, Nat.add_zero, beq_dec]
      generalize (X >>> (7 * e)) &&& 127 = A
      generalize (linL (AR 0) X >>> (7 * e)) &&& 127 = B
      by_cases h1 : A = 0 <;> by_cases h2 : A = B <;> simp [h1, h2, xor_eq_zero]
    · simp [hwe]
  · rw [zl_eq, flg_and]
    apply flg_congr
    intro e he
    by_cases hwe : F e >>> 7 = w
    · rw [hss e he hwe, hsq e he hwe, h4, ln_xor]
      simp only [hwe, decide_true, Bool.true_and, Nat.mul_zero, Nat.add_zero]
      have hp0 := Nat.pos_of_ne_zero hp
      have : ∀ A : ℕ, A + 128 * p ≠ 0 := fun A => by omega
      simp [this, beq_dec, hp]
    · simp [hwe]
  · symm
    apply flg_false
    intro e he
    by_cases hwe : F e >>> 7 = w
    · rw [hss e he hwe]
      simp only [hwe, decide_true, Bool.true_and, decide_eq_false_iff_not, not_and]
      intro _
      omega
    · simp [hwe]

include hmul hF hz hlin hFm hOm hcov in
theorem unI_eq {g : ℕ} (hg : g < 512) :
    unI AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g)) z
        (Om.map (fibOf F)) =
      flg fun e => decide (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧
        e + 128 * (g + 512) ≠ 0) := by
  have key : ∀ L : List ℕ, (∀ w ∈ L, w < 512) →
      unI AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g))
        z (L.map (fibOf F)) =
      flg fun e => decide (F e >>> 7 ∈ L) && decide (usq F z (mul := mul) e g = 0) := by
    intro L
    induction L with
    | nil =>
      intro _
      symm
      exact flg_false fun e _ => by simp
    | cons w L ih =>
      intro hL
      change Nat.lor _ (unI AR MR _ _ _ _ z (L.map (fibOf F))) = _
      rw [ih fun v hv => hL v (List.mem_cons_of_mem _ hv),
        fibI_eq AR MR F z hmul hF hz hlin hFm hg (hL w List.mem_cons_self), nl_or, flg_or]
      apply flg_congr
      intro e _
      simp only [List.mem_cons]
      by_cases h1 : F e >>> 7 = w <;> by_cases h2 : F e >>> 7 ∈ L <;> simp [h1, h2]
  rw [key Om hOm]
  apply flg_congr
  intro e he
  rw [ext_uu (mul := mul) F z e g]
  have : e + 128 * (g + 512) ≠ 0 := by omega
  simp only [hcov e he, this, usq, decide_true, Bool.true_and, ne_eq, not_false_eq_true, and_true]
  rfl

include hmul hF hz hlin hFm hOm hcov in
theorem unO_eq {g : ℕ} (hg : g < 512) :
    unO AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g)) z
        (Om.map (fibOf F)) =
      flg fun e => decide (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) ≠ 0 ∧
        extMulF 65536 mul F z (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)))
          (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512))) = 0) := by
  have key : ∀ L : List ℕ, (∀ w ∈ L, w < 512) →
      unO AR MR (AR g) (MR g) (linL (AR g) (lanesK (fun e => Nat.land (F e) 127) 128)) (F (Nat.mul 128 g))
        z (L.map (fibOf F)) =
      flg fun e => decide (F e >>> 7 ∈ L) && decide (usq F z (mul := mul) e g ≠ 0 ∧
        mul (usq F z (mul := mul) e g) (usq F z (mul := mul) e g) = 0) := by
    intro L
    induction L with
    | nil =>
      intro _
      symm
      exact flg_false fun e _ => by simp
    | cons w L ih =>
      intro hL
      change Nat.lor _ (unO AR MR _ _ _ _ z (L.map (fibOf F))) = _
      rw [ih fun v hv => hL v (List.mem_cons_of_mem _ hv),
        fibO_eq AR MR F z hmul hF hz hlin hFm hg (hL w List.mem_cons_self), nl_or, flg_or]
      apply flg_congr
      intro e _
      simp only [List.mem_cons]
      by_cases h1 : F e >>> 7 = w <;> by_cases h2 : F e >>> 7 ∈ L <;> simp [h1, h2]
  rw [key Om hOm]
  apply flg_congr
  intro e he
  rw [ext_uu (mul := mul) F z e g]
  have ha : e + 128 * g < 65536 := by omega
  have hs := mul_lt AR MR hmul (mul_lt AR MR hmul ha (hF _ ha)) hz
  have hss : extMulF 65536 mul F z (mul (mul (e + 128 * g) (F (e + 128 * g))) z)
      (mul (mul (e + 128 * g) (F (e + 128 * g))) z) =
      mul (mul (mul (e + 128 * g) (F (e + 128 * g))) z) (mul (mul (e + 128 * g) (F (e + 128 * g))) z) := by
    rw [extMulF_eq]
    unfold extMul
    rw [if_pos hs, if_pos hs]
  rw [hss]
  simp only [hcov e he, usq, decide_true, Bool.true_and, ne_eq]
  rfl

include hmul hF hz hlin hFm hOm hcov in
theorem grpW_eq {g : ℕ} (hg : g < 512) (Q U : List ℕ) (nQ : ℕ) :
    grpW mul AR MR F z (lanesK (fun e => Nat.land (F e) 127) 128) (Om.map (fibOf F)) Q U nQ g =
      grpU mul AR MR F z Q U nQ g := by
  unfold grpU
  rw [zIU_eq AR MR F z hmul hF hz g hg, zOU_eq AR MR F z hmul hF hz g hg]
  unfold grpW
  simp only [cen_strictN]
  rw [unI_eq AR MR F z hmul hF hz hlin hOm hcov hFm hg, unO_eq AR MR F z hmul hF hz hlin hOm hcov hFm hg]

end Grp

theorem blkW_eq {AR MR : ℕ → ℕ} {mul : ℕ → ℕ → ℕ} {F : ℕ → ℕ} {z : ℕ}
    (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d)
    (hF : ∀ a < 65536, F a < 65536) (hz : z < 65536) (hlin : ∀ h < 512, linOK (AR h) = true)
    {Om : List ℕ} (hOm : ∀ w ∈ Om, w < 512) (hcov : ∀ e < 128, F e >>> 7 ∈ Om)
    (hFm : ∀ e < 128, ∀ g < 512, F (e + 128 * g) = mul (F e) (F (128 * g)))
    (Q U : List ℕ) (nQ : ℕ) {t : ℕ} (ht : t < 8) :
    blkW mul AR MR F z Om Q U nQ t = blkU mul AR MR F z Q U nQ t := by
  unfold blkW
  simp only [cen_strictN]
  rw [recMap, natRec_sum]
  unfold blkU
  rw [natRec_sum]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.1 hj
  exact grpW_eq AR MR F z hmul hF hz hlin hOm hcov hFm (by simp only [Nat.add_eq, Nat.mul_eq]; omega) Q U nQ

end CFSG.KC.SBCenV

end
