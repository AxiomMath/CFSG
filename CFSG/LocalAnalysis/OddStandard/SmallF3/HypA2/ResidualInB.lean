module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ClassS
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.Open

private theorem ordA_one_mul_two {q : ℕ} (hq : Odd q) : ordA 1 q * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  unfold ordA
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, hg]
  apply Nat.div_mul_cancel
  have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    omega
  rw [h1]
  exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _

private theorem eq_of_ordA_one_eq {q q' : ℕ} (hq : Odd q) (hq' : Odd q')
    (h : ordA 1 q = ordA 1 q') : q = q' := by
  have h1 := ordA_one_mul_two hq
  have h2 := ordA_one_mul_two hq'
  have h3 : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1) := by rw [← h1, ← h2, h]
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  have hq1' : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ hq'.pos
  have h4 : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = (q' : ℤ) * ((q' : ℤ) ^ 2 - 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h3
    simp only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hq1', Nat.cast_pow,
      Nat.cast_one] at this
    exact this
  have hp : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hp' : (0 : ℤ) < q' := by exact_mod_cast hq'.pos
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · have hlt' : (q : ℤ) < q' := by exact_mod_cast hlt
    nlinarith [mul_pos (sub_pos.mpr hlt') (show (0 : ℤ) < q' ^ 2 + q * q' + q ^ 2 - 1 by
      nlinarith)]
  · exact heq
  · have hgt' : (q' : ℤ) < q := by exact_mod_cast hgt
    nlinarith [mul_pos (sub_pos.mpr hgt') (show (0 : ℤ) < q ^ 2 + q * q' + q' ^ 2 - 1 by
      nlinarith)]

theorem inSB_of_psl_two_three_eight {K : Type} [Group K] (h : LieModel K .PSL 2 3 8) :
    InSB K := by
  have hcard8 : Nat.card K = ordA 1 (3 ^ 8) :=
    GH74.card_of_lieModel_PSL (G := K) (n := 2) (p := 3) (f := 8) (by norm_num) h
  refine ⟨⟨.PSL, 2, 8, h⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard8]
    decide
  · exact ⟨3, .PSL, 2, by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h⟩
  · intro e he
    have hcarde : Nat.card K = ordA 1 (3 ^ e) :=
      GH74.card_of_lieModel_PSL (G := K) (n := 2) (p := 3) (f := e) (by norm_num) he
    have heq : 3 ^ e = 3 ^ 8 :=
      eq_of_ordA_one_eq (show Odd (3 ^ e) by exact (show Odd 3 by exact ⟨1, by norm_num⟩).pow)
        (show Odd (3 ^ 8) by exact (show Odd 3 by exact ⟨1, by norm_num⟩).pow)
        (hcarde.symm.trans hcard8)
    have he8 : e = 8 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
    exact ⟨3, by rw [he8]; norm_num⟩
  · intro h'
    have hcardD : Nat.card K = ordD 4 (3 ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := K) (t := .POmegaPlus)
        (n := 4) (p := 3) (f := 1) (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (G := K) (t := .POmegaPlus) (n := 4) (p := 3)
          (f := 1) (by norm_num) h')).2.2.2.2.1 rfl
    exact absurd (hcard8.symm.trans hcardD) (by decide)
  · intro h''
    have hcardD : Nat.card K = ordTwistedD 4 (3 ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := K) (t := .POmegaMinus)
        (n := 4) (p := 3) (f := 1) (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (G := K) (t := .POmegaMinus) (n := 4) (p := 3)
          (f := 1) (by norm_num) h'')).2.2.2.2.2 rfl
    exact absurd (hcard8.symm.trans hcardD) (by decide)

end CFSG.OddStandard.SmallF3.HypA2
