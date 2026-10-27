module

public import CFSG.Quasithin.Background.FFC3Unitri
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LargeExtraspecial.DW.D73

open Matrix

theorem exists_card_GL_eq {K : Type*} [Field K] [Finite K] {s : ℕ} (hK : Nat.card K = 2 ^ s)
    (k : ℕ) : ∃ u : ℕ, Odd u ∧ Nat.card (GL (Fin k) K) = 2 ^ (s * (k * (k - 1) / 2)) * u := by
  classical
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field]
  have hq : Fintype.card K = 2 ^ s := by rw [Fintype.card_eq_nat_card]; exact hK
  have hs : s ≠ 0 := by
    rintro rfl
    have h1 := Fintype.one_lt_card (α := K)
    rw [hq, pow_zero] at h1
    exact lt_irrefl 1 h1
  refine ⟨∏ i : Fin k, ((2 ^ s) ^ (k - i) - 1), ?_, ?_⟩
  · refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => ?_
    have hpos : k - (i : ℕ) ≠ 0 := by have := i.isLt; omega
    refine Nat.Even.sub_odd ?_ ?_ odd_one
    · exact Nat.one_le_pow _ _ (pow_pos two_pos s)
    · rw [← pow_mul]
      exact (Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero hs hpos⟩)
  · rw [hq]
    have hfac : ∀ i : Fin k, (2 ^ s) ^ k - (2 ^ s) ^ (i : ℕ) =
        (2 ^ s) ^ (i : ℕ) * ((2 ^ s) ^ (k - i) - 1) := by
      intro i
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.isLt.le]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id,
      ← pow_mul]

theorem le_of_two_pow_dvd_card_GL {K : Type*} [Field K] [Finite K] {s : ℕ}
    (hK : Nat.card K = 2 ^ s) {k a : ℕ} (h : 2 ^ a ∣ Nat.card (GL (Fin k) K)) :
    a ≤ s * (k * (k - 1) / 2) := by
  obtain ⟨u, hu, hcard⟩ := exists_card_GL_eq hK k
  rw [hcard] at h
  have hcop : Nat.Coprime (2 ^ a) u := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hu)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right h)

theorem eq_bot_of_normal_of_isPGroup (k : ℕ) (P : Subgroup (GL (Fin k) (ZMod 2)))
    (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ :=
  CFSG.Quasithin.FFC.eq_bot_of_normal_isPGroup h2

end CFSG.LargeExtraspecial.DW.D73
