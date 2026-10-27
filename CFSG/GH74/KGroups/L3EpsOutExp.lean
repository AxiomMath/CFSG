module

public import CFSG.GH74.KGroups.L3EpsWreathModels
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Exp

variable {X : Type*} [Group X] [Finite X]

theorem pow_mem_inner_of_outer {σ : MulAut X} {k n : ℕ} (hσ : σ ^ 2 ^ k = 1)
    (hN : ordProj[2] (Nat.card (Outer X)) ≤ 2 ^ n) : σ ^ 2 ^ n ∈ inner X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : MulAut X →* Outer X := QuotientGroup.mk' (inner X)
  have hπk : π σ ^ 2 ^ k = 1 := by rw [← map_pow, hσ, map_one]
  have hord : orderOf (π σ) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.2 hπk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hS : IsPGroup 2 (Subgroup.zpowers (π σ)) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
  have hdvd : Nat.card (Subgroup.zpowers (π σ)) ∣ ordProj[2] (Nat.card (Outer X)) :=
    card_dvd_ordProj hS
  rw [Nat.card_zpowers] at hdvd
  have h2n : orderOf (π σ) ∣ 2 ^ n := by
    refine hdvd.trans ?_
    show 2 ^ (Nat.card (Outer X)).factorization 2 ∣ 2 ^ n
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).1 hN)
  have : π (σ ^ 2 ^ n) = 1 := by rw [map_pow]; exact orderOf_dvd_iff_pow_eq_one.1 h2n
  exact (QuotientGroup.eq_one_iff _).1 this

end Exp

section Numeric

theorem four_mul_ordProj_le {p f : ℕ} (hp : Odd p) (h5 : 5 ≤ p ^ f) (h1 : p ^ f % 4 = 1) :
    4 * ordProj[2] f ≤ ordProj[2] (p ^ f - 1) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hN : p ^ f - 1 ≠ 0 := by omega
  rcases Nat.even_or_odd f with hfe | hfo
  · have hp1 : 1 < p := by
      by_contra h
      have hp1' : p ≤ 1 := by omega
      have : p ^ f ≤ 1 := by
        calc p ^ f ≤ 1 ^ f := Nat.pow_le_pow_left hp1' f
          _ = 1 := one_pow f
      omega
    have hp2 : ¬ 2 ∣ p := by
      rcases hp with ⟨k, rfl⟩
      omega
    have h := padicValNat.pow_two_sub_one_ge hp1 hp2 hf0 hfe
    show 4 * 2 ^ f.factorization 2 ≤ 2 ^ (p ^ f - 1).factorization 2
    rw [Nat.factorization_def f Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
    calc 4 * 2 ^ padicValNat 2 f = 2 ^ (padicValNat 2 f + 2) := by ring
      _ ≤ 2 ^ padicValNat 2 (p ^ f - 1) := Nat.pow_le_pow_right (by norm_num) h
  · rw [ordProj_two_eq_one_of_odd hfo, mul_one]
    obtain ⟨n, hn⟩ := ordProj_two_eq_four_mul hN (by omega)
    rw [hn]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

end Numeric

section Models

variable {X : Type} [Group X] {p f : ℕ}

theorem l3eps_outer_two_le {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hcong : (t = .PSL → p ^ f % 4 = 1) ∧ (t = .PSU → p ^ f % 4 = 3))
    (hX : StatedClassicalModel X t 3 p f) {n : ℕ}
    (hs : (t = .PSL → ordProj[2] (p ^ f - 1) = 4 * 2 ^ n) ∧
      (t = .PSU → ordProj[2] (p ^ f + 1) = 4 * 2 ^ n)) :
    ordProj[2] (Nat.card (Outer X)) ≤ 2 ^ (n + 1) := by
  have hp : p.Prime := hX.1.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases ht with rfl | rfl
  · have h1 := hcong.1 rfl
    have hsn := hs.1 rfl
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at h5
    have hg : Odd (Nat.gcd 3 (p ^ f - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
    have hg0 : Nat.gcd 3 (p ^ f - 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
    have hne : 2 * f * Nat.gcd 3 (p ^ f - 1) ≠ 0 := by positivity
    have h4 := four_mul_ordProj_le hpodd h5 h1
    rw [hsn] at h4
    have hfle : ordProj[2] f ≤ 2 ^ n := by omega
    refine (ordProj_two_le_of_dvd hne (lin_outer_dvd hX)).trans ?_
    rw [Nat.ordProj_mul 2 (by positivity) hg0, Nat.ordProj_mul 2 two_ne_zero hf0,
      ordProj_two_eq_one_of_odd hg, Nat.Prime.factorization_self Nat.prime_two]
    simp only [pow_one, mul_one]
    calc 2 * ordProj[2] f ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 hfle
      _ = 2 ^ (n + 1) := by ring
  · have h3 := hcong.2 rfl
    have hfo : Odd f := odd_of_pow_mod_four_eq_three hpodd h3
    have hf0 : f ≠ 0 := by rintro rfl; exact absurd hfo (by decide)
    have hg : Odd (Nat.gcd 3 (p ^ f + 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
    have hg0 : Nat.gcd 3 (p ^ f + 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
    have hout := (unitary_model_outer_two_part_bound X 3 p f hX).2.2.1
    rw [hout, Nat.ordProj_mul 2 (by positivity) hg0, Nat.ordProj_mul 2 two_ne_zero hf0,
      ordProj_two_eq_one_of_odd hg, ordProj_two_eq_one_of_odd hfo,
      Nat.Prime.factorization_self Nat.prime_two]
    calc 2 ^ 1 * 1 * 1 = 2 := by norm_num
      _ ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem finite_of_model {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X t 3 p f) : Finite X := by
  rcases ht with rfl | rfl
  · exact (lin_model_card hp2 hX).1
  · exact (uni_model_card hp2 hX).1

theorem l3eps_pow_mem_inner {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hcong : (t = .PSL → p ^ f % 4 = 1) ∧ (t = .PSU → p ^ f % 4 = 3))
    (hX : StatedClassicalModel X t 3 p f) {n : ℕ}
    (hs : (t = .PSL → ordProj[2] (p ^ f - 1) = 4 * 2 ^ n) ∧
      (t = .PSU → ordProj[2] (p ^ f + 1) = 4 * 2 ^ n)) {σ : MulAut X} {k : ℕ}
    (hσ : σ ^ 2 ^ k = 1) : σ ^ 2 ^ (n + 1) ∈ inner X := by
  have : Finite X := finite_of_model ht hp2 hX
  exact pow_mem_inner_of_outer hσ (l3eps_outer_two_le ht hp2 h5 hcong hX hs)

end Models

end CFSG.GH74.KGroups.L3Eps
