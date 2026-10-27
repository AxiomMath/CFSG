module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitArith

public section

namespace CFSG.SeitzReduction.RankOne

section NormWeight

variable {K : Type*} [Field K] [Fintype K]

theorem exists_eq_of_biadditive_equivariant {f : ℕ} (hf : 2 ≤ f)
    (hK : Fintype.card K = (2 ^ f) ^ 2) (β : K →+ K →+ K) {μ : K} (hμ0 : μ ≠ 0)
    (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hβ : ∀ a b, β (μ * a) (μ * b) = μ ^ (2 ^ f + 1) * β a b) :
    ∃ γ γ' : K, ∀ a b, β a b = γ * (a * b ^ 2 ^ f) + γ' * (a ^ 2 ^ f * b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [Nat.card_eq_fintype_card, hK']
  obtain ⟨-, hb, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases Nat.prime_two
      (n := 2 * f) (by omega) hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (2 * f - 1) < Fintype.card K := by
    rw [hK']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i j : Fin (2 * f),
      c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = c i j * μ ^ (2 ^ f + 1) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) - c i j * μ ^ (2 ^ f + 1))
      fun u w => by
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
          _ = μ ^ (2 ^ f + 1) * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hzero : ∀ i j : Fin (2 * f),
      ¬ (((i : ℕ) = 0 ∧ (j : ℕ) = f) ∨ ((i : ℕ) = f ∧ (j : ℕ) = 0)) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    apply hij
    refine eq_zero_f_of_dvd_two_pow_add_two_pow hf i.2 j.2 hμ ?_ ?_
    · rcases Nat.lt_or_ge (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) (2 ^ f + 1) with hlt' | hge
      · rw [Nat.sub_eq_zero_of_le hlt'.le]
        exact dvd_zero _
      · apply orderOf_dvd_of_pow_eq_one
        have e : μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
            μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - (2 ^ f + 1)) * μ ^ (2 ^ f + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hge]
        rw [e] at h1
        exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1.trans (one_mul _).symm)
    · rcases Nat.lt_or_ge (2 ^ f + 1) (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) with hlt' | hge
      · rw [Nat.sub_eq_zero_of_le hlt'.le]
        exact dvd_zero _
      · apply orderOf_dvd_of_pow_eq_one
        have e : μ ^ (2 ^ f + 1) =
            μ ^ (2 ^ f + 1 - (2 ^ (i : ℕ) + 2 ^ (j : ℕ))) * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) := by
          rw [← pow_add, Nat.sub_add_cancel hge]
        rw [e] at h1
        exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1.symm.trans (one_mul _).symm)
  set i0 : Fin (2 * f) := ⟨0, by omega⟩ with hi0
  set iF : Fin (2 * f) := ⟨f, by omega⟩ with hiF
  have hne : i0 ≠ iF := by
    intro h
    have := congrArg Fin.val h
    simp only [hi0, hiF] at this
    omega
  refine ⟨c i0 iF, c iF i0, fun a b => ?_⟩
  rw [hc a b]
  rw [Fintype.sum_eq_add i0 iF hne (fun i hi => Finset.sum_eq_zero fun j _ => by
    rw [hzero i j (by
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hi.1 (Fin.ext h1)
      · exact hi.2 (Fin.ext h1)), zero_mul])]
  rw [Finset.sum_eq_single iF (fun j _ hj => by
      rw [hzero i0 j (by
        rintro (⟨-, h1⟩ | ⟨h1, -⟩)
        · exact hj (Fin.ext h1)
        · simp only [hi0] at h1
          omega), zero_mul]) (by simp),
    Finset.sum_eq_single i0 (fun j _ hj => by
      rw [hzero iF j (by
        rintro (⟨h1, -⟩ | ⟨-, h1⟩)
        · simp only [hiF] at h1
          omega
        · exact hj (Fin.ext h1)), zero_mul]) (by simp)]
  simp only [hi0, hiF, pow_zero, pow_one]

theorem exists_eq_of_biadditive_equivariant' {f : ℕ} (hf : 2 ≤ f)
    (hK : Fintype.card K = (2 ^ f) ^ 2) (B : K → K → K)
    (hB₁ : ∀ a a' b, B (a + a') b = B a b + B a' b) (hB₂ : ∀ a b b', B a (b + b') = B a b + B a b')
    {μ : K} (hμ0 : μ ≠ 0) (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hB : ∀ a b, B (μ * a) (μ * b) = μ ^ (2 ^ f + 1) * B a b) :
    ∃ γ γ' : K, ∀ a b, B a b = γ * (a * b ^ 2 ^ f) + γ' * (a ^ 2 ^ f * b) := by
  let β : K →+ K →+ K := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (B a) (hB₂ a)) fun a a' => by
    ext b
    exact hB₁ a a' b
  exact exists_eq_of_biadditive_equivariant hf hK β hμ0 hμ hB

theorem apply_swap_semilinear_eq {f : ℕ} (hK : Fintype.card K = (2 ^ f) ^ 2) (γ γ' m : K)
    (hm : m * m ^ 2 ^ f = 1) (a b : K) :
    γ * ((m * b ^ 2 ^ f) * (m * a ^ 2 ^ f) ^ 2 ^ f) +
        γ' * ((m * b ^ 2 ^ f) ^ 2 ^ f * (m * a ^ 2 ^ f)) =
      γ * (a * b ^ 2 ^ f) + γ' * (a ^ 2 ^ f * b) := by
  have hfrob : ∀ x : K, (x ^ 2 ^ f) ^ 2 ^ f = x := by
    intro x
    rw [← pow_mul, ← sq, ← hK]
    exact FiniteField.pow_card x
  rw [mul_pow, mul_pow, hfrob a, hfrob b]
  linear_combination (γ * a * b ^ 2 ^ f + γ' * a ^ 2 ^ f * b) * hm

end NormWeight

end CFSG.SeitzReduction.RankOne
