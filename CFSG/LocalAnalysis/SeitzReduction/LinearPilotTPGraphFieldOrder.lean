module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField)

theorem isCoprime_sq_add_add_one_pow_add_one (q : ℤ) (i : ℕ) :
    IsCoprime (q ^ 2 + q + 1) (q ^ i + 1) := by
  have hq : IsCoprime (q ^ 2 + q + 1) q := ⟨1, -(q + 1), by ring⟩
  have hq1 : IsCoprime (q ^ 2 + q + 1) (q + 1) := ⟨1, -q, by ring⟩
  have h2 : IsCoprime (q ^ 2 + q + 1) 2 := by
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self q
    exact ⟨1, -m, by linear_combination hm⟩
  have hdvd : ∀ k : ℕ, (q ^ 2 + q + 1) ∣ q ^ (3 * k) - 1 := by
    intro k
    have h1 : q ^ 3 - 1 ∣ (q ^ 3) ^ k - 1 ^ k := sub_dvd_pow_sub_pow _ _ k
    rw [one_pow, ← pow_mul] at h1
    exact (Dvd.intro_left (q - 1) (by ring)).trans h1
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < 3 ∧ i = 3 * k + t :=
    ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 3).symm⟩
  obtain ⟨w, hw⟩ := hdvd k
  have heq : q ^ (3 * k + t) + 1 = (q ^ t + 1) + (q ^ 2 + q + 1) * (q ^ t * w) := by
    rw [pow_add]
    linear_combination (q ^ t) * hw
  rw [heq]
  refine IsCoprime.add_mul_left_right ?_ _
  interval_cases t
  · rw [pow_zero, one_add_one_eq_two]
    exact h2
  · rw [pow_one]
    exact hq1
  · have h3 : q ^ 2 + 1 = -q + (q ^ 2 + q + 1) * 1 := by ring
    rw [h3]
    exact hq.neg_right.add_mul_left_right 1

theorem false_of_mul_eq_prod (q : ℤ) (hq : 2 ≤ q) {n : ℕ} (hn : 3 ≤ n) (N : ℕ) {M d d' : ℤ}
    (hd : 0 < d) (hdq : d ∣ q - 1)
    (hL : M * d = q ^ N * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1))
    (hU : M * d' = q ^ N * ∏ i ∈ Finset.Icc 2 n, (q ^ i - (-1) ^ i)) : False := by
  set s := Finset.Icc 2 n with hs
  set A := ∏ i ∈ s with Odd i, (q ^ i - 1) with hA
  set B := ∏ i ∈ s with Odd i, (q ^ i + 1) with hB
  set E := ∏ i ∈ s with ¬ Odd i, (q ^ i - 1) with hE
  have hSL : ∏ i ∈ s, (q ^ i - 1) = A * E := (Finset.prod_filter_mul_prod_filter_not s Odd _).symm
  have hSU : ∏ i ∈ s, (q ^ i - (-1) ^ i) = B * E := by
    rw [← Finset.prod_filter_mul_prod_filter_not s Odd]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.1 hi).2.neg_one_pow, sub_neg_eq_add]
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [(Nat.not_odd_iff_even.1 (Finset.mem_filter.1 hi).2).neg_one_pow]
  have hE0 : E ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1
    have h1 : (1 : ℤ) < q ^ i := one_lt_pow₀ (by omega) (by omega)
    exact sub_ne_zero.2 (ne_of_gt h1)
  have hqN : q ^ N ≠ 0 := pow_ne_zero _ (by omega)
  have hAB : A * d' = B * d := by
    have h1 : q ^ N * E * (A * d') = q ^ N * E * (B * d) := by
      calc q ^ N * E * (A * d') = q ^ N * (A * E) * d' := by ring
        _ = M * d * d' := by rw [hL, hSL]
        _ = M * d' * d := by ring
        _ = q ^ N * (B * E) * d := by rw [hU, hSU]
        _ = q ^ N * E * (B * d) := by ring
    exact mul_left_cancel₀ (mul_ne_zero hqN hE0) h1
  have hrA : q ^ 2 + q + 1 ∣ A := by
    have h3 : 3 ∈ s.filter Odd :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by norm_num, hn⟩, by decide⟩
    exact (Dvd.intro_left (q - 1) (by ring : (q - 1) * (q ^ 2 + q + 1) = q ^ 3 - 1)).trans
      (Finset.dvd_prod_of_mem _ h3)
  have hrB : IsCoprime (q ^ 2 + q + 1) B :=
    IsCoprime.prod_right fun i _ => isCoprime_sq_add_add_one_pow_add_one q i
  have hrd : q ^ 2 + q + 1 ∣ d := by
    refine hrB.dvd_of_dvd_mul_left ?_
    rw [← hAB]
    exact hrA.mul_right d'
  have h1 : q ^ 2 + q + 1 ≤ d := Int.le_of_dvd hd hrd
  have h2 : d ≤ q - 1 := Int.le_of_dvd (by omega) hdq
  nlinarith

theorem card_projectiveSL_not_dvd_card_unitarySU {p e n : ℕ} {k K : Type} [Field k] [Finite k]
    [Field K] (h : UnitaryFieldData p e K) (hk : Nat.card k = p ^ e) (hn : 3 ≤ n) :
    ¬ Nat.card (projectiveSL n k) ∣ Nat.card (unitarySU p e K n) := by
  rintro ⟨d', hd'⟩
  have hq : 2 ≤ p ^ e := by
    have := h.prime.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right h.prime.pos h.one_le
  have hSL := card_SL_eq (K := k) (n := n) (by omega)
  rw [(scalars n k).card_eq_card_quotient_mul_card_subgroup] at hSL
  have hdvd := card_scalars_dvd (K := k) (n := n) (by omega)
  obtain ⟨hSU, -⟩ := card_unitarySU_and_factorization h (n := n) (by omega)
  refine false_of_mul_eq_prod ((p ^ e : ℕ) : ℤ) (by exact_mod_cast hq) hn (n * (n - 1) / 2)
    (M := (Nat.card (projectiveSL n k) : ℤ)) (d := (Nat.card (scalars n k) : ℤ))
    (d' := (d' : ℤ)) (by exact_mod_cast Nat.card_pos) ?_ ?_ ?_
  · rw [← hk]
    have h1 : 1 ≤ Nat.card k := Nat.card_pos
    have h2 := Int.natCast_dvd_natCast.2 hdvd
    rwa [Nat.cast_sub h1, Nat.cast_one] at h2
  · rw [← hk]
    have h1 : ((Nat.card k ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (Nat.card k ^ j - 1) :
        ℕ) : ℤ) = ((Nat.card k : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
          ∏ j ∈ Finset.Icc 2 n, (((Nat.card k : ℕ) : ℤ) ^ j - 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.cast_one]
    rw [← h1, ← hSL]
    push_cast
    ring
  · rw [← hSU, hd']
    push_cast
    ring

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_unitaryFieldData_of_graphField {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {τ : K ≃+* K} (hτ1 : τ ≠ 1) (hτ : (fieldAut n K τ * dualAut n K) ^ 2 = 1) :
    ∃ (e : ℕ) (h : UnitaryFieldData 2 e K), f = 2 * e ∧ ∀ x, τ x = h.bar x := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨⟨e, he⟩, hτx, -⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two
    hf hK hn 1 τ hτ1 (by rwa [map_one, one_mul])
  have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
  refine ⟨e, hud, by omega, fun x => ?_⟩
  rw [hτx, UnitaryFieldData.bar_apply, show f / 2 = e by omega]

theorem fieldCoreNeGraphFieldCore {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) :
    FieldCoreNeGraphFieldCore n K := by
  intro σ τ hσ1 hσ hτ1 hτ Γ _ φ₁ φ₂ hφ₁ hφ₂
  obtain ⟨e, hud, hfe, hτbar⟩ := exists_unitaryFieldData_of_graphField hK hn hτ1 hτ
  have hk : Nat.card (fixedField K σ) = 2 ^ e := by
    have h1 := card_fixedField_sq hK hσ1 hσ
    rw [hK, hfe, pow_mul'] at h1
    exact Nat.pow_left_injective (by norm_num) h1
  refine map_perfectCore_fieldAut_ne_of_card_ne hK hn hσ hφ₁ hφ₂ fun hcard => ?_
  have h1 := card_perfectCore_graphField_dvd hud hn τ hτbar
  rw [hcard] at h1
  exact card_projectiveSL_not_dvd_card_unitarySU hud hk hn h1

theorem transvectionIntrinsicStdField {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    TransvectionIntrinsicStdField n K :=
  transvectionIntrinsicStdField_of_graphField hK hn (fieldCoreNeGraphFieldCore hK (by omega))

end CFSG.SeitzReduction.LinearPilot
