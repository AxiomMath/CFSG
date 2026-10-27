module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {P : Subgroup G} {a b : G}

private theorem fzrAux_addP_lo (p q : ℕ) : addP p q % 8 = (p % 8 + q % 8) % 8 := by
  simp only [addP]; omega

private theorem fzrAux_addP_hi (p q : ℕ) :
    addP p q / 8 % 8 = (p / 8 % 8 + q / 8 % 8) % 8 := by
  simp only [addP]; omega

private theorem fzrAux_addP_lt (p q : ℕ) : addP p q < 64 := by
  simp only [addP]; omega

private theorem fzrAux_subP_lt (p q : ℕ) : subP p q < 64 := by
  simp only [subP]; omega

private theorem fzrAux_addP_subP_zero (n : ℕ) (hn : n < 64) : addP n (subP 0 n) = 0 := by
  simp only [addP, subP]; omega

private theorem fzrAux_addP_subP_eq_subP (n m : ℕ) (hn : n < 64) (hm : m < 64) :
    addP n (subP 0 m) = subP n m := by
  simp only [addP, subP]; omega

private theorem fzrAux_addP_add_eq_zero_iff_inZ (n : ℕ) :
    addP n n = 0 ↔ inZ n = true := by
  simp only [addP, inZ, Bool.and_eq_true, beq_iff_eq]; omega

private theorem fzrAux_addP4_eq_zero_iff (n : ℕ) :
    addP (addP n n) (addP n n) = 0 ↔ (n % 2 = 0 ∧ n / 8 % 2 = 0) := by
  simp only [addP]; omega

private theorem fzrAux_elt_mul' (hcomm : a * b = b * a) (ha8 : a ^ 8 = 1) (hb8 : b ^ 8 = 1)
    (x x' y y' : ℕ) :
    (a ^ x * b ^ y) * (a ^ x' * b ^ y') = a ^ ((x + x') % 8) * b ^ ((y + y') % 8) := by
  have hcomm' : b ^ y * a ^ x' = a ^ x' * b ^ y :=
    ((show Commute a b from hcomm).symm.pow_pow y x').eq
  calc
    (a ^ x * b ^ y) * (a ^ x' * b ^ y')
        = a ^ x * (b ^ y * (a ^ x' * b ^ y')) := mul_assoc _ _ _
    _ = a ^ x * ((b ^ y * a ^ x') * b ^ y') := by
          rw [← mul_assoc (b ^ y) (a ^ x') (b ^ y')]
    _ = a ^ x * ((a ^ x' * b ^ y) * b ^ y') := by rw [hcomm']
    _ = a ^ x * (a ^ x' * (b ^ y * b ^ y')) := by
          rw [mul_assoc (a ^ x') (b ^ y) (b ^ y')]
    _ = (a ^ x * a ^ x') * (b ^ y * b ^ y') := by
          rw [← mul_assoc (a ^ x) (a ^ x') (b ^ y * b ^ y')]
    _ = a ^ (x + x') * b ^ (y + y') := by rw [pow_add, pow_add]
    _ = a ^ ((x + x') % 8) * b ^ ((y + y') % 8) := by
          rw [pow_eq_pow_mod (n := 8) (x + x') ha8, pow_eq_pow_mod (n := 8) (y + y') hb8]

theorem fzr_a_elt_zero : fzrAElt a b 0 = 1 := by
  simp only [fzrAElt, Nat.zero_mod, Nat.zero_div, pow_zero, mul_one]

theorem fzr_a_elt_mem (hB : FzR10ABasis P a b) (n : ℕ) : fzrAElt a b n ∈ P := by
  simp only [fzrAElt]
  exact P.mul_mem (P.pow_mem hB.a_mem _) (P.pow_mem hB.b_mem _)

theorem fzr_a_elt_mul (hB : FzR10ABasis P a b) {n m : ℕ} (hn : n < 64) (hm : m < 64) :
    fzrAElt a b n * fzrAElt a b m = fzrAElt a b (addP n m) := by
  simp only [fzrAElt]
  rw [fzrAux_elt_mul' hB.comm hB.a8 hB.b8, fzrAux_addP_lo, fzrAux_addP_hi]

theorem fzr_a_elt_inv (hB : FzR10ABasis P a b) {n : ℕ} (hn : n < 64) :
    (fzrAElt a b n)⁻¹ = fzrAElt a b (subP 0 n) := by
  apply inv_eq_of_mul_eq_one_right
  rw [fzr_a_elt_mul hB hn (fzrAux_subP_lt 0 n), fzrAux_addP_subP_zero n hn]
  exact fzr_a_elt_zero

theorem fzr_a_elt_sq (hB : FzR10ABasis P a b) {n : ℕ} (hn : n < 64) :
    fzrAElt a b n ^ 2 = fzrAElt a b (addP n n) := by
  rw [pow_two, fzr_a_elt_mul hB hn hn]

theorem fzr_a_elt_div (hB : FzR10ABasis P a b) {n m : ℕ} (hn : n < 64) (hm : m < 64) :
    fzrAElt a b n * (fzrAElt a b m)⁻¹ = fzrAElt a b (subP n m) := by
  rw [fzr_a_elt_inv hB hm, fzr_a_elt_mul hB hn (fzrAux_subP_lt 0 m),
      fzrAux_addP_subP_eq_subP n m hn hm]

theorem fzr_a_elt_eq_iff (hB : FzR10ABasis P a b) {n m : ℕ} (hn : n < 64) (hm : m < 64) :
    fzrAElt a b n = fzrAElt a b m ↔ n = m := by
  constructor
  · intro h
    exact hB.inj n m hn hm h
  · intro h
    rw [h]

theorem fzr_a_elt_eq_one_iff (hB : FzR10ABasis P a b) {n : ℕ} (hn : n < 64) :
    fzrAElt a b n = 1 ↔ n = 0 := by
  have h1 : (1 : G) = fzrAElt a b 0 := (fzr_a_elt_zero).symm
  rw [h1]
  exact fzr_a_elt_eq_iff hB hn (by omega)

theorem fzr_a_elt_sq_eq_one_iff (hB : FzR10ABasis P a b) {n : ℕ} (hn : n < 64) :
    fzrAElt a b n ^ 2 = 1 ↔ inZ n = true := by
  rw [fzr_a_elt_sq hB hn, fzr_a_elt_eq_one_iff hB (fzrAux_addP_lt n n)]
  exact fzrAux_addP_add_eq_zero_iff_inZ n

theorem fzr_a_elt_pow4_eq_one_iff (hB : FzR10ABasis P a b) {n : ℕ} (hn : n < 64) :
    fzrAElt a b n ^ 4 = 1 ↔ (n % 2 = 0 ∧ n / 8 % 2 = 0) := by
  have hpow : fzrAElt a b n ^ 4 = fzrAElt a b (addP (addP n n) (addP n n)) := by
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, fzr_a_elt_sq hB hn,
        fzr_a_elt_sq hB (fzrAux_addP_lt n n)]
  rw [hpow, fzr_a_elt_eq_one_iff hB (fzrAux_addP_lt (addP n n) (addP n n))]
  exact fzrAux_addP4_eq_zero_iff n

end CFSG.OddStandard.SmallF3.FritzII
