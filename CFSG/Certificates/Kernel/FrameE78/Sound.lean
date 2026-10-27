module

public import Certificates.Data.Kernel.FrameE78K
public import Mathlib.Algebra.BigOperators.Ring.Finset
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS.PK

theorem beqT {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem bltT {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

theorem notB_eq (b : Bool) : notB b = !b := by
  cases b <;> rfl

theorem bitB_eq (M i : ℕ) : bitB M i = M.testBit i := hasBit_eq M i

private theorem land3 (x : ℕ) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

private theorem shr2 (x : ℕ) : x >>> 2 = x / 4 := Nat.shiftRight_eq_div_pow x 2

private theorem lt_pow_of {c k i : ℕ} (hc : c < 2 ^ k) (h : k ≤ i) : c < 2 ^ i :=
  lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) h)

private theorem four_pow (n : ℕ) : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
  rw [pow_mul]
  rfl

@[expose] def VOK (n x : ℕ) : Prop := x < 4 ^ n ∧ ∀ q < n, ln x q ≤ 2

theorem ln_eq (x q : ℕ) : ln x q = x / 4 ^ q % 4 := by
  have h := fld_eq x (2 * q) 2
  rw [← four_pow] at h
  exact h

theorem ln_zero (x : ℕ) : ln x 0 = x % 4 := by
  rw [ln_eq, pow_zero, Nat.div_one]

theorem ln_succ (x q : ℕ) : ln x (q + 1) = ln (x / 4) q := by
  rw [ln_eq, ln_eq, pow_succ', Nat.div_div_eq_div_mul]

theorem ln_add4 {r : ℕ} (hr : r < 4) (m q : ℕ) :
    ln (r + 4 * m) q = if q = 0 then r else ln m (q - 1) := by
  cases q with
  | zero => rw [ln_zero, if_pos rfl]; omega
  | succ q =>
    rw [ln_succ, if_neg (Nat.succ_ne_zero q), Nat.add_sub_cancel]
    congr 1
    omega

theorem ln_bits (x q : ℕ) :
    ln x q = (x.testBit (2 * q)).toNat + 2 * (x.testBit (2 * q + 1)).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, ln_eq, pow_succ,
    ← Nat.div_div_eq_div_mul, ← four_pow]
  generalize x / 4 ^ q = y
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 2) with h' | h' <;> simp [h, h'] <;> omega

theorem ln_zero_bits {x q : ℕ} (h : ln x q = 0) :
    x.testBit (2 * q) = false ∧ x.testBit (2 * q + 1) = false := by
  rw [ln_bits] at h
  revert h
  cases x.testBit (2 * q) <;> cases x.testBit (2 * q + 1) <;> decide

theorem ln_or_left {a b q : ℕ} (hb : ln b q = 0) : ln (a ||| b) q = ln a q := by
  obtain ⟨h0, h1⟩ := ln_zero_bits hb
  rw [ln_bits, ln_bits a, Nat.testBit_or, Nat.testBit_or, h0, h1, Bool.or_false, Bool.or_false]

theorem ln_or_right {a b q : ℕ} (ha : ln a q = 0) : ln (a ||| b) q = ln b q := by
  rw [Nat.or_comm]
  exact ln_or_left ha

theorem ln_shl {v : ℕ} (hv : v < 4) (k q : ℕ) :
    ln (v <<< (2 * k)) q = if q = k then v else 0 := by
  rw [ln_bits, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  rcases lt_trichotomy q k with h | rfl | h
  · rw [if_neg (by omega)]
    simp only [ge_iff_le, decide_eq_false (by omega : ¬ 2 * q ≥ 2 * k),
      decide_eq_false (by omega : ¬ 2 * q + 1 ≥ 2 * k), Bool.false_and]
    rfl
  · rw [if_pos rfl]
    simp only [ge_iff_le, le_refl, decide_true, Bool.true_and, Nat.sub_self,
      decide_eq_true (by omega : 2 * q ≤ 2 * q + 1), Nat.add_sub_cancel_left]
    have h := ln_bits v 0
    rw [ln_zero, Nat.mod_eq_of_lt hv, Nat.mul_zero, Nat.zero_add] at h
    exact h.symm
  · rw [if_neg (by omega)]
    have hv' : v < 2 ^ 2 := hv
    have e0 : v.testBit (2 * q - 2 * k) = false :=
      Nat.testBit_lt_two_pow (lt_pow_of hv' (by omega))
    have e1 : v.testBit (2 * q + 1 - 2 * k) = false :=
      Nat.testBit_lt_two_pow (lt_pow_of hv' (by omega))
    rw [e0, e1, Bool.and_false, Bool.and_false]
    rfl

private theorem ln_zero_val (q : ℕ) : ln 0 q = 0 := by
  rw [ln_eq, Nat.zero_div]

theorem ln_pack (g : ℕ → ℕ) : ∀ k q, ln (Nat.rec (motive := fun _ => ℕ) 0
    (fun p ih => ih ||| (g p % 3) <<< (2 * p)) k) q = if q < k then g q % 3 else 0
  | 0, q => by
    rw [if_neg (Nat.not_lt_zero q)]
    exact ln_zero_val q
  | k + 1, q => by
    have hv : g k % 3 < 4 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    change ln (Nat.rec (motive := fun _ => ℕ) 0
      (fun p ih => ih ||| (g p % 3) <<< (2 * p)) k ||| (g k % 3) <<< (2 * k)) q = _
    by_cases hq : q = k
    · subst hq
      rw [ln_or_right (by rw [ln_pack g q q, if_neg (Nat.lt_irrefl q)]), ln_shl hv, if_pos rfl,
        if_pos (Nat.lt_succ_self q)]
    · rw [ln_or_left (by rw [ln_shl hv, if_neg hq]), ln_pack g k q]
      by_cases hk : q < k
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk, if_neg (by omega)]

theorem VOK_zero {x : ℕ} : VOK 0 x ↔ x = 0 := by
  unfold VOK
  rw [pow_zero]
  exact ⟨fun h => by omega, fun h => ⟨by omega, fun q hq => absurd hq (Nat.not_lt_zero q)⟩⟩

theorem VOK_succ {n x : ℕ} : VOK (n + 1) x ↔ x % 4 ≤ 2 ∧ VOK n (x / 4) := by
  unfold VOK
  rw [Nat.div_lt_iff_lt_mul (by decide), ← pow_succ]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun q hq => ?_⟩
    · rw [← ln_zero]
      exact h2 0 (Nat.succ_pos n)
    · rw [← ln_succ]
      exact h2 (q + 1) (by omega)
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun q hq => ?_⟩
    cases q with
    | zero =>
      rw [ln_zero]
      exact h0
    | succ q =>
      rw [ln_succ]
      exact h2 q (by omega)

theorem VOK_ext : ∀ {n x y : ℕ}, VOK n x → VOK n y → (∀ q < n, ln x q = ln y q) → x = y
  | 0, x, y, hx, hy, _ => by rw [VOK_zero] at hx hy; rw [hx, hy]
  | n + 1, x, y, hx, hy, h => by
    rw [VOK_succ] at hx hy
    have h0 := h 0 (Nat.succ_pos n)
    rw [ln_zero, ln_zero] at h0
    have h1 := VOK_ext hx.2 hy.2 fun q hq => by
      have h2 := h (q + 1) (by omega)
      rwa [ln_succ, ln_succ] at h2
    omega

private theorem bits21845 : ∀ q < 8, Nat.testBit 21845 (2 * q) = true := by decide

theorem validV_sound {n x : ℕ} (hn : n ≤ 8) (h : validV n x = true) : VOK n x := by
  unfold validV at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun q hq => ?_⟩
  · rw [four_pow]
    exact (shiftRight_eq_zero_iff x (2 * n)).1 (beqT.1 h1)
  · have h3 : ((x &&& x >>> 1) &&& 21845).testBit (2 * q) = false := by
      have h2' : (x &&& x >>> 1 &&& 21845) = 0 := beqT.1 h2
      rw [h2']
      exact Nat.zero_testBit _
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, bits21845 q (by omega),
      Bool.and_true, Nat.add_comm 1] at h3
    have h4 := ln_bits x q
    revert h3 h4
    cases x.testBit (2 * q) <;> cases x.testBit (2 * q + 1) <;> intro h3 h4 <;> simp_all

private theorem bitsNeg : ∀ q < 8, Nat.testBit 21845 (2 * q) = true ∧
    Nat.testBit 21845 (2 * q + 1) = false ∧ Nat.testBit 43690 (2 * q + 2) = false ∧
    Nat.testBit 43690 (2 * q + 1) = true := by decide

theorem ln_negL {y q : ℕ} (hq : q < 8) (hy : ln y q ≤ 2) :
    ln (negL y) q = (3 - ln y q) % 3 := by
  obtain ⟨c0, c1, c2, c3⟩ := bitsNeg q hq
  have hb0 : (negL y).testBit (2 * q) = y.testBit (2 * q + 1) := by
    change (((y &&& 21845) <<< 1) ||| ((y &&& 43690) >>> 1)).testBit (2 * q) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and,
      Nat.testBit_and, Nat.add_comm 1, c3, Bool.and_true]
    cases q with
    | zero => simp
    | succ q =>
      have c4 := (bitsNeg q (by omega)).2.1
      rw [show 2 * (q + 1) - 1 = 2 * q + 1 by omega, c4]
      simp
  have hb1 : (negL y).testBit (2 * q + 1) = y.testBit (2 * q) := by
    change (((y &&& 21845) <<< 1) ||| ((y &&& 43690) >>> 1)).testBit (2 * q + 1) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and,
      Nat.testBit_and, Nat.add_sub_cancel, c0, show 1 + (2 * q + 1) = 2 * q + 2 by omega, c2]
    simp
  rw [ln_bits (negL y), hb0, hb1]
  rw [ln_bits] at hy ⊢
  revert hy
  cases y.testBit (2 * q) <;> cases y.testBit (2 * q + 1) <;> decide

theorem normV_ite (n x : ℕ) : normV n x = if lead n x = 2 then negL x else x := by
  change Bool.rec (motive := fun _ => ℕ) x (negL x) (Nat.beq (lead n x) 2) = _
  rw [nIf_eq]
  simp only [beqT]

theorem normV_eq (n x : ℕ) : normV n x = x ∨ normV n x = negL x := by
  rw [normV_ite]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem lead_zero (x : ℕ) : lead 0 x = 0 := rfl

theorem lead_succ (n x : ℕ) :
    lead (n + 1) x = if x % 4 = 0 then lead n (x / 4) else x % 4 := by
  change strictN (x &&& 3)
    (fun a => Bool.rec (motive := fun _ => ℕ) a (lead n (x >>> 2)) (Nat.beq a 0)) = _
  rw [strictN_eq, nIf_eq, land3, shr2]
  simp only [beqT]

theorem lead_spec : ∀ (n x : ℕ), (lead n x = 0 ∧ ∀ q < n, ln x q = 0) ∨
    ∃ q0 < n, lead n x = ln x q0 ∧ ln x q0 ≠ 0 ∧ ∀ q < q0, ln x q = 0
  | 0, x => Or.inl ⟨rfl, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
  | n + 1, x => by
    rw [lead_succ]
    by_cases h0 : x % 4 = 0
    · rw [if_pos h0]
      rcases lead_spec n (x / 4) with ⟨h1, h2⟩ | ⟨q0, hq0, h1, h2, h3⟩
      · refine Or.inl ⟨h1, fun q hq => ?_⟩
        cases q with
        | zero => rw [ln_zero]; exact h0
        | succ q => rw [ln_succ]; exact h2 q (by omega)
      · refine Or.inr ⟨q0 + 1, by omega, by rw [ln_succ]; exact h1, by rw [ln_succ]; exact h2,
          fun q hq => ?_⟩
        cases q with
        | zero => rw [ln_zero]; exact h0
        | succ q => rw [ln_succ]; exact h3 q (by omega)
    · rw [if_neg h0]
      exact Or.inr ⟨0, Nat.succ_pos n, by rw [ln_zero], by rw [ln_zero]; exact h0,
        fun q hq => absurd hq (Nat.not_lt_zero q)⟩

private theorem sum_range_four (f : ℕ → ℕ) : ∀ m, ∑ x ∈ Finset.range (4 * m), f x =
    ∑ y ∈ Finset.range m, (f (4 * y) + f (4 * y + 1) + f (4 * y + 2) + f (4 * y + 3))
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ _ m, ← sum_range_four f m,
      show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.add_assoc]

private theorem card_eq_sum (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    ((Finset.range k).filter p).card = ∑ x ∈ Finset.range k, if p x then 1 else 0 := by
  rw [Finset.card_filter]

private theorem VOK_four (n y a : ℕ) (ha : a < 4) :
    VOK (n + 1) (4 * y + a) ↔ a ≤ 2 ∧ VOK n y := by
  rw [VOK_succ, show (4 * y + a) % 4 = a by omega, show (4 * y + a) / 4 = y by omega]

private theorem lead_four (n y a : ℕ) (ha : a < 4) :
    lead (n + 1) (4 * y + a) = if a = 0 then lead n y else a := by
  rw [lead_succ, show (4 * y + a) % 4 = a by omega, show (4 * y + a) / 4 = y by omega]

noncomputable instance (n x : ℕ) : Decidable (VOK n x) :=
  inferInstanceAs (Decidable (x < 4 ^ n ∧ ∀ q < n, ln x q ≤ 2))

private theorem card_vok : ∀ n, ((Finset.range (4 ^ n)).filter (VOK n)).card = 3 ^ n
  | 0 => by
    rw [card_eq_sum, pow_zero, pow_zero, Finset.sum_range_one, if_pos (VOK_zero.2 rfl)]
  | n + 1 => by
    rw [card_eq_sum, pow_succ', sum_range_four, pow_succ', ← card_vok n, card_eq_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h0 : VOK (n + 1) (4 * y) ↔ VOK n y := by
      have := VOK_four n y 0 (by decide)
      simpa using this
    by_cases h : VOK n y <;> simp [h0, VOK_four n y 1 (by decide), VOK_four n y 2 (by decide),
      VOK_four n y 3 (by decide), h]

theorem card_norm : ∀ n,
    2 * ((Finset.range (4 ^ n)).filter (fun x => VOK n x ∧ lead n x = 1)).card + 1 = 3 ^ n
  | 0 => by
    rw [card_eq_sum, pow_zero, pow_zero, Finset.sum_range_one, if_neg (fun h => by
      rw [lead_zero] at h; exact absurd h.2 (by decide))]
    rfl
  | n + 1 => by
    have ih := card_norm n
    have hv := card_vok n
    rw [card_eq_sum] at ih hv ⊢
    rw [pow_succ', sum_range_four, pow_succ']
    have e : ∀ y, ((if VOK (n + 1) (4 * y) ∧ lead (n + 1) (4 * y) = 1 then 1 else 0) +
        (if VOK (n + 1) (4 * y + 1) ∧ lead (n + 1) (4 * y + 1) = 1 then 1 else 0) +
        (if VOK (n + 1) (4 * y + 2) ∧ lead (n + 1) (4 * y + 2) = 1 then 1 else 0) +
        (if VOK (n + 1) (4 * y + 3) ∧ lead (n + 1) (4 * y + 3) = 1 then 1 else 0) : ℕ) =
        (if VOK n y ∧ lead n y = 1 then 1 else 0) + (if VOK n y then 1 else 0) := by
      intro y
      have h0 : VOK (n + 1) (4 * y) ↔ VOK n y := by
        have := VOK_four n y 0 (by decide)
        simpa using this
      have l0 : lead (n + 1) (4 * y) = lead n y := by
        have := lead_four n y 0 (by decide)
        simpa using this
      have h1 := VOK_four n y 1 (by decide)
      have l1 := lead_four n y 1 (by decide)
      have h2 := VOK_four n y 2 (by decide)
      have l2 := lead_four n y 2 (by decide)
      have h3 := VOK_four n y 3 (by decide)
      by_cases h : VOK n y <;> by_cases hl : lead n y = 1 <;>
        simp [h0, l0, h1, l1, h2, l2, h3, h, hl]
    rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib]
    omega

private theorem rec_sum (f : ℕ → ℕ) : ∀ n, Nat.rec (motive := fun _ => ℕ) 0
    (fun q ih => ih + f q) n = ∑ q ∈ Finset.range n, f q
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← rec_sum f n]

theorem dot3_eq (n u v : ℕ) : dot3 n u v = (∑ q ∈ Finset.range n, ln u q * ln v q) % 3 :=
  congrArg (· % 3) (rec_sum (fun q => ln u q * ln v q) n)

theorem ln_cvec {n p : ℕ} (C c : ℕ) (hp : p < n) :
    ln (cvec n C c) p = (∑ q ∈ Finset.range n, cij C p q * ln c q) % 3 := by
  have h := ln_pack (fun p => Nat.rec (motive := fun _ => ℕ) 0
    (fun q ih' => ih' + cij C p q * ln c q) n) n p
  rw [if_pos hp, rec_sum] at h
  exact h

theorem ln_sV {n C j x p : ℕ} (hp : p < n) (hx : ln x p ≤ 2) :
    ln (sV n C j x) p = (ln x p + 2 * (ln x j * cij C p j)) % 3 := by
  change ln (strictN (ln x j) fun xj => Bool.rec (motive := fun _ => ℕ)
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun p ih => ih ||| ((ln x p + 2 * (xj * cij C p j)) % 3) <<< (2 * p)) n)
    x (Nat.beq xj 0)) p = _
  rw [strictN_eq, nIf_eq]
  by_cases h0 : ln x j = 0
  · rw [if_pos (beqT.2 h0), h0, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    omega
  · rw [if_neg (fun h => h0 (beqT.1 h)), ln_pack (fun p => ln x p + 2 * (ln x j * cij C p j)) n p,
      if_pos hp]

theorem pack_lt (g : ℕ → ℕ) : ∀ k, Nat.rec (motive := fun _ => ℕ) 0
    (fun p ih => ih ||| (g p % 3) <<< (2 * p)) k < 4 ^ k
  | 0 => Nat.pow_pos (by decide : 0 < 4)
  | k + 1 => by
    change Nat.rec (motive := fun _ => ℕ) 0
      (fun p ih => ih ||| (g p % 3) <<< (2 * p)) k ||| (g k % 3) <<< (2 * k) < 4 ^ (k + 1)
    rw [four_pow]
    apply Nat.or_lt_two_pow
    · have := pack_lt g k
      rw [four_pow] at this
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
    · rw [Nat.shiftLeft_eq, ← four_pow, ← four_pow, pow_succ, mul_comm (4 ^ k)]
      exact Nat.mul_lt_mul_of_pos_right (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
        (Nat.pow_pos (by decide : 0 < 4))

theorem VOK_sV {n C j y : ℕ} (hy : VOK n y) : VOK n (sV n C j y) := by
  change VOK n (strictN (ln y j) fun xj => Bool.rec (motive := fun _ => ℕ)
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun p ih => ih ||| ((ln y p + 2 * (xj * cij C p j)) % 3) <<< (2 * p)) n)
    y (Nat.beq xj 0))
  rw [strictN_eq, nIf_eq]
  split
  · exact hy
  · refine ⟨pack_lt _ n, fun q hq => ?_⟩
    rw [ln_pack, if_pos hq]
    omega

private theorem ln_clear : ∀ (i c q : ℕ),
    ln (c - ln c i * 4 ^ i) q = if q = i then 0 else ln c q
  | 0, c, q => by
    rw [ln_zero, pow_zero, Nat.mul_one, show c - c % 4 = 0 + 4 * (c / 4) by omega,
      ln_add4 (by decide)]
    cases q with
    | zero => rfl
    | succ q => rw [if_neg (Nat.succ_ne_zero q), if_neg (Nat.succ_ne_zero q), ln_succ,
        Nat.add_sub_cancel]
  | i + 1, c, q => by
    rw [ln_succ]
    have hle : ln (c / 4) i * 4 ^ i ≤ c / 4 := by
      rw [ln_eq]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self _ _)
    have e : c - ln (c / 4) i * 4 ^ (i + 1) = c % 4 + 4 * (c / 4 - ln (c / 4) i * 4 ^ i) := by
      rw [pow_succ', Nat.mul_left_comm]
      generalize ln (c / 4) i * 4 ^ i = A at hle ⊢
      omega
    rw [e, ln_add4 (Nat.mod_lt _ (by decide))]
    cases q with
    | zero => rw [if_pos rfl, if_neg (by omega), ln_zero]
    | succ q =>
      rw [if_neg (Nat.succ_ne_zero q), Nat.add_sub_cancel, ln_clear i (c / 4) q, ln_succ]
      by_cases hq : q = i
      · rw [if_pos hq, if_pos (by omega)]
      · rw [if_neg hq, if_neg (by omega)]

theorem ln_sRt (c Cc i q : ℕ) :
    ln (sRt c Cc i) q = if q = i then (ln c i + 2 * ln Cc i) % 3 else ln c q := by
  have hv : (ln c i + 2 * ln Cc i) % 3 < 4 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have e : c - ln c i <<< (2 * i) = c - ln c i * 4 ^ i := by
    rw [Nat.shiftLeft_eq, four_pow]
  change ln ((c - ln c i <<< (2 * i)) ||| ((ln c i + 2 * ln Cc i) % 3) <<< (2 * i)) q = _
  rw [e]
  by_cases hq : q = i
  · subst hq
    rw [ln_or_right (by rw [ln_clear, if_pos rfl]), ln_shl hv, if_pos rfl, if_pos rfl]
  · rw [ln_or_left (by rw [ln_shl hv, if_neg hq]), ln_clear, if_neg hq, if_neg hq]

theorem ptsOK_sound {n N V : ℕ} (hn : n ≤ 8) (h : ptsOK n N V = true) :
    2 * N = 3 ^ n - 1 ∧ ∀ i < N, VOK n (vget V i) ∧ lead n (vget V i) = 1 ∧
      (i + 1 < N → vget V i < vget V (i + 1)) := by
  unfold ptsOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨beqT.1 h1, fun i hi => ?_⟩
  have h3 := allN_iff.1 h2 i hi
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h3
  obtain ⟨hv, hl, hs⟩ := h3
  rw [bIf_eq] at hs
  refine ⟨validV_sound hn hv, beqT.1 hl, fun hi1 => ?_⟩
  rw [if_pos (bltT.2 hi1)] at hs
  exact bltT.1 hs

theorem ptsOK_lt {n N V : ℕ} (hn : n ≤ 8) (h : ptsOK n N V = true) :
    ∀ i j, i < j → j < N → vget V i < vget V j := by
  have hs := (ptsOK_sound hn h).2
  intro i j hij hj
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    have hstep := (hs j (by omega)).2.2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact lt_trans (ih h' (by omega)) hstep
    · exact hstep

theorem ptsOK_complete {n N V : ℕ} (hn : n ≤ 8) (h : ptsOK n N V = true) {x : ℕ}
    (hx : VOK n x) (hl : lead n x = 1) : ∃ i < N, vget V i = x := by
  obtain ⟨hN, hs⟩ := ptsOK_sound hn h
  have hlt := ptsOK_lt hn h
  set T := (Finset.range (4 ^ n)).filter (fun x => VOK n x ∧ lead n x = 1) with hT
  have hcard : T.card = N := by
    have := card_norm n
    rw [← hT] at this
    omega
  have hsub : (Finset.range N).image (vget V) ⊆ T := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2, -⟩ := hs i hi
    rw [hT, Finset.mem_filter, Finset.mem_range]
    exact ⟨h1.1, h1, h2⟩
  have hinj : Set.InjOn (vget V) (Finset.range N : Set ℕ) := by
    intro i hi j hj e
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e (ne_of_lt (hlt i j h' hj))
    · exact h'
    · exact absurd e (ne_of_gt (hlt j i h' hi))
  have heq : (Finset.range N).image (vget V) = T := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcard]
  have hxT : x ∈ T := by
    rw [hT, Finset.mem_filter, Finset.mem_range]
    exact ⟨hx.1, hx, hl⟩
  rw [← heq, Finset.mem_image] at hxT
  obtain ⟨i, hi, e⟩ := hxT
  exact ⟨i, Finset.mem_range.1 hi, e⟩

theorem genJ_sound {n C N : ℕ} {S : List ℕ} {V j : ℕ} (h : genJ n C N S V j = true) :
    ∀ q < N, pg 12 4095 (getS S j) q < N ∧
      vget V (pg 12 4095 (getS S j) q) = normV n (sV n C j (vget V q)) := by
  intro q hq
  unfold genJ at h
  rw [strictB_eq] at h
  have h1 := allN_iff.1 h q hq
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨bltT.1 h1.1, beqT.1 h1.2⟩

private theorem shr16_or {c z : ℕ} (hc : c < 2 ^ 16) : (c ||| z <<< 16) >>> 16 = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))),
    Nat.add_sub_cancel_left]
  simp

theorem rootOK_sound {n C m RP : ℕ} (hn : n ≤ 8) (h : rootOK n C m RP = true) :
    ∀ a < m, VOK n (rc RP a) ∧ rC RP a = cvec n C (rc RP a) ∧
      dot3 n (rc RP a) (cvec n C (rc RP a)) = 2 := by
  intro a ha
  have h1 := allN_iff.1 h a ha
  rw [strictB_eq] at h1
  simp only [bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨hv, hr, hd⟩ := h1
  have hV := validV_sound hn hv
  have hc : rc RP a < 2 ^ 16 :=
    lt_of_lt_of_le hV.1 (by rw [four_pow]; exact Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hV, ?_, beqT.1 hd⟩
  change rget RP a >>> 16 = _
  rw [beqT.1 hr]
  exact shr16_or hc

theorem simpleOK_sound {n RP : ℕ} (h : simpleOK n RP = true) :
    ∀ i < n, rc RP i = 1 <<< (2 * i) := fun i hi => beqT.1 (allN_iff.1 h i hi)

theorem closOK_sound {n m RP CL : ℕ} (h : closOK n m RP CL = true) :
    ∀ a < m, ∀ i < n, clget CL a i < m ∧
      (sRt (rc RP a) (rC RP a) i = rc RP (clget CL a i) ∨
        sRt (rc RP a) (rC RP a) i = negL (rc RP (clget CL a i))) := by
  intro a ha i hi
  have h1 := allN_iff.1 (allN_iff.1 h a ha) i hi
  rw [strictB_eq, strictB_eq, bAnd_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, beqT,
    beqT] at h1
  exact ⟨bltT.1 h1.1, h1.2⟩

theorem parOK_sound {n m CL PT : ℕ} (h : parOK n m CL PT = true) :
    ∀ a, n ≤ a → a < m → ∃ p < a, ∃ i < n, clget CL p i = a := by
  intro a hna ham
  have hlt : a - n < Nat.sub m n := by
    change a - n < m - n
    omega
  have e : Nat.add n (a - n) = a := by
    change n + (a - n) = a
    omega
  have h1 := allN_iff.1 h (a - n) hlt
  rw [strictB_eq, e, strictB_eq, strictB_eq, strictB_eq] at h1
  simp only [bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨hp, hi, he⟩ := h1
  exact ⟨_, bltT.1 hp, _, bltT.1 hi, beqT.1 he⟩

theorem distOK_sound {m RP : ℕ} (h : distOK m RP = true) :
    ∀ a < m, ∀ b < a, rc RP a ≠ rc RP b ∧ rc RP a ≠ negL (rc RP b) := by
  intro a ha b hb
  have h1 := allN_iff.1 h a ha
  rw [strictB_eq] at h1
  have h2 := allN_iff.1 h1 b hb
  rw [strictB_eq, bAnd_eq, notB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true'] at h2
  exact ⟨fun e => by rw [e, Nat.beq_refl] at h2; exact Bool.noConfusion h2.1,
    fun e => by rw [e, Nat.beq_refl] at h2; exact Bool.noConfusion h2.2⟩

theorem coverOK_sound {N k : ℕ} {D : List ℕ} (h : coverOK N k D = true) :
    ∀ p < N, ∃ t < k, depD (getS D t) p ≠ 255 := by
  intro p hp
  have h1 := allN_iff.1 h p hp
  rw [notB_eq, Bool.not_eq_true'] at h1
  by_contra hc
  push Not at hc
  have h2 : allN k (fun t => Nat.beq (depD (getS D t) p) 255) = true :=
    allN_iff.2 fun t ht => beqT.2 (hc t ht)
  rw [h1] at h2
  exact Bool.noConfusion h2

private theorem foldr_cnt (f : ℕ → Bool) : ∀ (l : List ℕ) (s : ℕ),
    l.foldr (fun i s => Bool.rec (motive := fun _ => ℕ) s (Nat.succ s) (f i)) s =
      s + (l.filter f).length
  | [], s => rfl
  | x :: l, s => by
    rw [List.foldr_cons, foldr_cnt f l, List.filter_cons]
    cases f x
    · rfl
    · rw [if_pos rfl, List.length_cons]
      rfl

theorem cntN_eq (m : ℕ) (f : ℕ → Bool) :
    cntN m f = ((Finset.range m).filter fun i => f i = true).card := by
  unfold cntN
  rw [foldN_eq, foldr_cnt, Nat.zero_add]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert, List.filter_cons, List.filter_nil]
    cases hf : f m
    · simp
    · rw [if_pos rfl, if_pos rfl, Finset.card_insert_of_notMem (fun hm => by
        rw [Finset.mem_filter, Finset.mem_range] at hm; exact Nat.lt_irrefl m hm.1)]
      rfl

theorem txOK_sound {n m RP x Tm : ℕ} (h : txOK n m RP x Tm = true) :
    Tm < 2 ^ m ∧ ∀ a < m, (Tm.testBit a = true ↔ dot3 n (rc RP a) x = 0) := by
  unfold txOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨(shiftRight_eq_zero_iff Tm m).1 (beqT.1 h.1), fun a ha => ?_⟩
  have h1 := allN_iff.1 h.2 a ha
  rw [bIf_eq, bitB_eq, notB_eq] at h1
  by_cases hd : dot3 n (rc RP a) x = 0
  · rw [if_pos (beqT.2 hd)] at h1
    exact ⟨fun _ => hd, fun _ => h1⟩
  · rw [if_neg (fun e => hd (beqT.1 e)), Bool.not_eq_true'] at h1
    exact ⟨fun e => absurd (h1 ▸ e) Bool.false_ne_true, fun e => absurd e hd⟩

theorem unifK_sound {n m RP Tm t d : ℕ} (h : unifK n m RP Tm t d = true) :
    ((Finset.range m).filter fun a => Tm.testBit a = true).card = t ∧
      ∀ a < m, Tm.testBit a = true → ((Finset.range m).filter fun b =>
        Tm.testBit b = true ∧ b ≠ a ∧ bf n RP a b ≠ 0).card = d := by
  unfold unifK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [beqT, cntN_eq] at h1
  simp only [bitB_eq] at h1
  refine ⟨h1, fun a ha hT => ?_⟩
  have h3 := allN_iff.1 h2 a ha
  rw [bIf_eq, bitB_eq, if_pos hT, beqT, cntN_eq] at h3
  rw [← h3]
  congr 1
  apply Finset.filter_congr
  intro b _
  simp only [bAnd_eq, bitB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', ne_eq]
  constructor
  · rintro ⟨h4, h5, h6⟩
    refine ⟨h4, ?_, ?_⟩
    · cases e : Nat.beq b a
      · rfl
      · exact absurd (beqT.1 e) h5
    · cases e : Nat.beq (bf n RP a b) 0
      · rfl
      · exact absurd (beqT.1 e) h6
  · rintro ⟨h4, h5, h6⟩
    exact ⟨h4, fun e => by rw [e, Nat.beq_refl] at h5; exact Bool.noConfusion h5,
      fun e => by rw [e] at h6; exact Bool.noConfusion h6⟩

theorem alwK_sound {n t d : ℕ} (h : alwK n t d = true) :
    (n = 7 ∧ (t = 21 ∧ d = 10 ∨ t = 30 ∧ d = 16 ∨ t = 36 ∧ d = 20)) ∨
      (n = 8 ∧ (t = 36 ∧ d = 14 ∨ t = 42 ∧ d = 20 ∨ t = 63 ∧ d = 32)) := by
  unfold alwK at h
  simp only [orB_eq, bAnd_eq, Bool.or_eq_true, Bool.and_eq_true, beqT] at h
  exact h

theorem splitK_sound {n m RP Tm P : ℕ} (h : splitK n m RP Tm P = true) :
    (∀ a, P.testBit a = true → Tm.testBit a = true) ∧ P ≠ 0 ∧ P ≠ Tm ∧
      ∀ a < m, ∀ b < m, P.testBit a = true → Tm.testBit b = true → P.testBit b = false →
        bf n RP a b = 0 := by
  unfold splitK at h
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [strictB_eq] at h4
  have hPT := beqT.1 h1
  refine ⟨fun a ha => ?_, fun e => ?_, fun e => ?_, fun a ha b hb hPa hTb hPb => ?_⟩
  · have e : (P &&& Tm).testBit a = P.testBit a := by rw [show (P &&& Tm) = P from hPT]
    rw [Nat.testBit_and, ha, Bool.true_and] at e
    exact e
  · rw [e, Nat.beq_refl] at h2
    exact Bool.noConfusion h2
  · rw [e, Nat.beq_refl] at h3
    exact Bool.noConfusion h3
  · have h5 := allN_iff.1 h4 a ha
    rw [bIf_eq, bitB_eq P a, if_pos hPa] at h5
    have h6 := allN_iff.1 h5 b hb
    have hx : bitB (Nat.xor Tm P) b = true := by
      rw [bitB_eq]
      change (Tm ^^^ P).testBit b = true
      rw [Nat.testBit_xor, hTb, hPb]
      rfl
    rw [bIf_eq, if_pos hx] at h6
    exact beqT.1 h6

theorem repK_sound {n m RP V b : ℕ} {Q : List ℕ} (h : repK n m RP V b Q = true) :
    txOK n m RP (vget V b) (getS Q 0) = true ∧
      ((getS Q 1 = 0 ∧ alwK n (getS Q 2) (getS Q 3) = true ∧
          unifK n m RP (getS Q 0) (getS Q 2) (getS Q 3) = true) ∨
        (getS Q 1 = 1 ∧ splitK n m RP (getS Q 0) (getS Q 2) = true)) := by
  unfold repK at h
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  by_cases hk : getS Q 1 = 0
  · rw [if_pos (beqT.2 hk), strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
    exact Or.inl ⟨hk, h2⟩
  · rw [if_neg (fun e => hk (beqT.1 e)), bAnd_eq, Bool.and_eq_true] at h2
    exact Or.inr ⟨beqT.1 h2.1, h2.2⟩

end CFSG.KC.FrameE78

end
