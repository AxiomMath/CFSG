module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsField
public import Mathlib.CategoryTheory.Category.Init

public section

namespace CFSG.SeitzReduction.RankOne

open Module

section Twist

variable {K : Type*} [Field K] [Fintype K]

theorem ne_zero_of_forall_pow_eq_of_two_le {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) : μ ≠ 0 := by
  classical
  rintro rfl
  obtain ⟨w, hw0, hw1⟩ : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
      by_cases hw : w = 0
      · simp [hw]
      · simp [hcon w hw]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, hK] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact absurd (h2.trans h1) (by norm_num)
  obtain ⟨m, hm⟩ := hμ w hw0
  rcases m with _ | m
  · exact hw1 (by rw [← hm, pow_zero])
  · exact hw0 (by rw [← hm, zero_pow (Nat.succ_ne_zero _)])

theorem orderOf_eq_of_forall_pow_eq {μ : K} (hμ0 : μ ≠ 0)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) : orderOf μ = Fintype.card K - 1 := by
  have hu : IsUnit μ := Ne.isUnit hμ0
  have hgen : ∀ w : Kˣ, w ∈ Subgroup.zpowers hu.unit := by
    intro w
    obtain ⟨m, hm⟩ := hμ w w.ne_zero
    exact ⟨m, Units.ext (by simp [hm])⟩
  have h1 : orderOf hu.unit = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hgen
  rw [Nat.card_units, Nat.card_eq_fintype_card] at h1
  rw [← h1, ← orderOf_units, IsUnit.unit_spec]

theorem eq_pred_of_dvd_two_pow_add_two_pow_sub_one {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : 2 ^ n - 1 ∣ 2 ^ i + 2 ^ j - 1) : i = n - 1 ∧ j = n - 1 := by
  have hi' : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1i : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hle : 2 ^ n - 1 ≤ 2 ^ i + 2 ^ j - 1 := Nat.le_of_dvd (by omega) h
  have hsum : 2 ^ i + 2 ^ j = 2 ^ n := by omega
  have hij := SzCoords.eq_of_two_pow_add_two_pow hsum
  subst hij
  have := SzCoords.eq_succ_of_two_pow_add_self hsum
  omega

theorem bilinear_eq_zero_of_alternating_equivariant {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (β : K →+ K →+ K) {μ : K} (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hβ : ∀ u w, β (μ * u) (μ * w) = μ * β u w) (halt : ∀ u, β u u = 0) : β = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      rw [pow_zero] at hK
      exact absurd hK (Fintype.one_lt_card (α := K)).ne'
    · exact h
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨-, hb, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases Nat.prime_two hn hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i j : Fin n,
      c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = c i j * μ := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) - c i j * μ) fun u w => by
        have h1 := hβ u w
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ i, ∑ j, c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) *
              (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) =
            ∑ i, ∑ j, c i j * ((μ * u) ^ 2 ^ (i : ℕ) * (μ * w) ^ 2 ^ (j : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow, mul_pow, pow_add]
              ring
          _ = μ * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hzero : ∀ i j : Fin n, ((i : ℕ) ≠ n - 1 ∨ (j : ℕ) ≠ n - 1) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have hn2 : 2 ≤ n := by omega
    have hμ0 := ne_zero_of_forall_pow_eq_of_two_le hK hn2 hμ
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    have h1i : 1 ≤ 2 ^ (i : ℕ) := Nat.one_le_two_pow
    have h1j : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
    have hE : μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) = 1 := by
      rw [show 2 ^ (i : ℕ) + 2 ^ (j : ℕ) = (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) + 1 by omega,
        pow_succ] at h1
      exact mul_right_cancel₀ hμ0 (h1.trans (one_mul μ).symm)
    have hdvd := orderOf_dvd_of_pow_eq_one hE
    rw [orderOf_eq_of_forall_pow_eq hμ0 hμ, hK] at hdvd
    have := eq_pred_of_dvd_two_pow_add_two_pow_sub_one i.2 j.2 hdvd
    omega
  have hlast : c ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 0 := by
    have h1 := halt 1
    rw [hc] at h1
    simp only [one_pow, mul_one] at h1
    rwa [Finset.sum_eq_single ⟨n - 1, by omega⟩ (fun i _ hi => Finset.sum_eq_zero fun j _ =>
      hzero i j (Or.inl fun h => hi (Fin.ext h))) (by simp),
      Finset.sum_eq_single ⟨n - 1, by omega⟩ (fun j _ hj =>
      hzero _ j (Or.inr fun h => hj (Fin.ext h))) (by simp)] at h1
  have hall : ∀ i j : Fin n, c i j = 0 := by
    intro i j
    by_cases hij : (i : ℕ) = n - 1 ∧ (j : ℕ) = n - 1
    · obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      obtain ⟨rfl, rfl⟩ := hij
      exact hlast
    · exact hzero i j (by tauto)
  refine AddMonoidHom.ext fun u => AddMonoidHom.ext fun w => ?_
  rw [hc]
  simp [hall]

theorem bilinear_eq_zero_of_alternating_equivariant' {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (β : K → K → K) (h1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (h2 : ∀ u w w', β u (w + w') = β u w + β u w') {μ : K}
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w)
    (hβ : ∀ u w, β (μ * u) (μ * w) = μ * β u w) (halt : ∀ u, β u u = 0) (u w : K) :
    β u w = 0 := by
  have h := bilinear_eq_zero_of_alternating_equivariant hK
    (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (β u) (h2 u))
      fun u u' => AddMonoidHom.ext fun w => h1 u u' w) hμ hβ halt
  exact congrArg (fun b : K →+ K →+ K => b u w) h

end Twist

end CFSG.SeitzReduction.RankOne
