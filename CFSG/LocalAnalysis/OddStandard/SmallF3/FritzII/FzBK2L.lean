module

public import Certificates.Data.FzBU
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU

@[expose] def fzbAlpha {G : Type} [Group G] (q s y : G) (w : ℕ) : G :=
  q ^ (w % 4) * s ^ (w / 4 % 2) * y ^ (w / 8)

private theorem fzb_q_pow_mod {G : Type} [Group G] {q : G} (hq : q ^ 4 = 1) (n : ℕ) :
    q ^ n = q ^ (n % 4) := pow_eq_pow_mod n hq

private theorem fzb_s_pow_mod {G : Type} [Group G] {s : G} (hs : s ^ 2 = 1) (n : ℕ) :
    s ^ n = s ^ (n % 2) := pow_eq_pow_mod n hs

private theorem fzb_y_pow_mod {G : Type} [Group G] {y : G} (hy : y ^ 2 = 1) (n : ℕ) :
    y ^ n = y ^ (n % 2) := pow_eq_pow_mod n hy

private theorem fzb_q_inv {G : Type} [Group G] {q : G} (hq : q ^ 4 = 1) : q⁻¹ = q ^ 3 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ' q 3, show (3 : ℕ) + 1 = 4 from by norm_num]
  exact hq

private theorem fzb_s_mul_q_pow {G : Type} [Group G] {q s : G} (hq : q ^ 4 = 1)
    (hsq : s * q * s⁻¹ = q⁻¹) (n : ℕ) : s * q ^ n = q ^ (3 * n) * s := by
  have hsq' : s * q = q⁻¹ * s := by
    rw [← hsq, mul_assoc, inv_mul_cancel, mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_succ, ← mul_assoc, ih, mul_assoc, hsq', fzb_q_inv hq,
      ← mul_assoc, ← pow_add q (3 * n) 3]

private theorem fzb_qs_mul {G : Type} [Group G] {q s : G} (hq : q ^ 4 = 1) (hs : s ^ 2 = 1)
    (hsq : s * q * s⁻¹ = q⁻¹) {i i' k k' : ℕ} (hk : k < 2) :
    (q ^ i * s ^ k) * (q ^ i' * s ^ k') =
      q ^ ((i + (if k = 0 then i' else 3 * i')) % 4) * s ^ ((k + k') % 2) := by
  interval_cases k
  · rw [pow_zero, mul_one, if_pos rfl, Nat.zero_add]
    rw [← mul_assoc, ← pow_add q i i', fzb_q_pow_mod hq (i + i'), fzb_s_pow_mod hs k']
  · rw [pow_one, if_neg (by decide : ¬ ((1 : ℕ) = 0))]
    calc
      (q ^ i * s) * (q ^ i' * s ^ k')
          = q ^ i * (s * (q ^ i' * s ^ k')) := mul_assoc _ _ _
      _ = q ^ i * ((s * q ^ i') * s ^ k') := by rw [← mul_assoc s (q ^ i') (s ^ k')]
      _ = q ^ i * ((q ^ (3 * i') * s) * s ^ k') := by rw [fzb_s_mul_q_pow hq hsq i']
      _ = q ^ i * (q ^ (3 * i') * (s * s ^ k')) := by
            rw [mul_assoc (q ^ (3 * i')) s (s ^ k')]
      _ = q ^ i * (q ^ (3 * i') * s ^ (k' + 1)) := by rw [← pow_succ']
      _ = (q ^ i * q ^ (3 * i')) * s ^ (k' + 1) := by rw [← mul_assoc]
      _ = q ^ (i + 3 * i') * s ^ (k' + 1) := by rw [← pow_add q i (3 * i')]
      _ = q ^ ((i + 3 * i') % 4) * s ^ ((1 + k') % 2) := by
            rw [fzb_q_pow_mod hq (i + 3 * i'), fzb_s_pow_mod hs (k' + 1),
              Nat.add_comm k' 1]

private theorem fzb_alpha_mul_gen {G : Type} [Group G] {q s y : G}
    (hq : q ^ 4 = 1) (hs : s ^ 2 = 1) (hy : y ^ 2 = 1)
    (hsq : s * q * s⁻¹ = q⁻¹) (hyq : y * q = q * y) (hys : y * s = s * y)
    {i i' k k' l l' : ℕ} (hk : k < 2) :
    (q ^ i * s ^ k * y ^ l) * (q ^ i' * s ^ k' * y ^ l') =
      q ^ ((i + (if k = 0 then i' else 3 * i')) % 4) *
        s ^ ((k + k') % 2) * y ^ ((l + l') % 2) := by
  have hyB : Commute (y ^ l) (q ^ i' * s ^ k') :=
    (Commute.pow_pow (show Commute y q from hyq) l i').mul_right
      (Commute.pow_pow (show Commute y s from hys) l k')
  calc
    (q ^ i * s ^ k * y ^ l) * (q ^ i' * s ^ k' * y ^ l')
        = (q ^ i * s ^ k) * (q ^ i' * s ^ k') * (y ^ l * y ^ l') := by
          rw [Commute.mul_mul_mul_comm hyB (q ^ i * s ^ k) (y ^ l')]
    _ = (q ^ i * s ^ k) * (q ^ i' * s ^ k') * y ^ (l + l') := by
          rw [← pow_add y l l']
    _ = (q ^ ((i + (if k = 0 then i' else 3 * i')) % 4) * s ^ ((k + k') % 2)) *
          y ^ (l + l') := by
          rw [fzb_qs_mul hq hs hsq (i := i) (i' := i') (k := k) (k' := k') hk]
    _ = q ^ ((i + (if k = 0 then i' else 3 * i')) % 4) * s ^ ((k + k') % 2) *
          y ^ ((l + l') % 2) := by
          rw [fzb_y_pow_mod hy (l + l')]

private theorem fzb_amul_arith (w w' : ℕ) (hw : w < 16) (hw' : w' < 16) :
    (w % 4 + (if w / 4 % 2 = 0 then w' % 4 else 3 * (w' % 4))) % 4 = amul w w' % 4 ∧
      (w / 4 % 2 + w' / 4 % 2) % 2 = amul w w' / 4 % 2 ∧
      (w / 8 + w' / 8) % 2 = amul w w' / 8 := by
  interval_cases w <;> interval_cases w' <;> decide

theorem fzb_alpha_mul {G : Type} [Group G] {q s y : G} (hq : q ^ 4 = 1) (hs : s ^ 2 = 1)
    (hy : y ^ 2 = 1) (hsq : s * q * s⁻¹ = q⁻¹) (hyq : y * q = q * y) (hys : y * s = s * y)
    {w w' : ℕ} (hw : w < 16) (hw' : w' < 16) :
    fzbAlpha q s y w * fzbAlpha q s y w' = fzbAlpha q s y (amul w w') := by
  obtain ⟨hA, hB, hC⟩ := fzb_amul_arith w w' hw hw'
  have hgen := fzb_alpha_mul_gen (q := q) (s := s) (y := y) hq hs hy hsq hyq hys
    (i := w % 4) (i' := w' % 4) (k := w / 4 % 2) (k' := w' / 4 % 2)
    (l := w / 8) (l' := w' / 8) (hk := Nat.mod_lt (w / 4) (by norm_num))
  simp only [fzbAlpha]
  rw [hgen, hA, hB, hC]

theorem fzb_alpha_zero {G : Type} [Group G] (q s y : G) : fzbAlpha q s y 0 = 1 := by
  simp only [fzbAlpha, Nat.zero_mod, Nat.zero_div, pow_zero, mul_one]

theorem fzb_alpha_gens {G : Type} [Group G] (q s y : G) :
    fzbAlpha q s y 1 = q ∧ fzbAlpha q s y 4 = s ∧ fzbAlpha q s y 8 = y ∧
      fzbAlpha q s y 2 = q ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [fzbAlpha]

end CFSG.OddStandard.SmallF3.FritzII
