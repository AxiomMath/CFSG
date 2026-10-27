module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalTypes
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormal

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Arith

theorem inner_pair_arith_even {f s v₁ v₂ w : ℕ} (hf : 2 ≤ f) (hw : w < f)
    (h1 : f * ((2 * s + 4) * (2 * s + 3)) ≤ 2 * v₁ + f * ((s + 2) * (s + 1)))
    (h2 : f * ((2 * s + 3) * (2 * s + 4)) ≤ 4 * v₂)
    (h3 : v₁ + v₂ ≤ f * ((s + 2) * (2 * s + 3)) + 2 + w) : False := by
  have key : f * (2 * s * s + 8 * s + 8) ≤ 8 + 4 * w := by nlinarith
  have h8 : f * 8 ≤ f * (2 * s * s + 8 * s + 8) := Nat.mul_le_mul_left f (by omega)
  omega

theorem inner_pair_arith_odd {f s v₁ v₂ w : ℕ} (hf : 2 ≤ f) (hw : w < f)
    (h1 : f * ((2 * s + 5) * (2 * s + 4)) ≤ 2 * v₁ + f * ((s + 2) * (s + 1)))
    (h2 : f * ((2 * s + 4) * (2 * s + 4)) ≤ 4 * v₂)
    (h3 : v₁ + v₂ ≤ f * ((2 * s + 5) * (s + 2)) + 2 + w) : False := by
  have key : f * (2 * s * s + 10 * s + 12) ≤ 8 + 4 * w := by nlinarith
  have h8 : f * 12 ≤ f * (2 * s * s + 10 * s + 12) := Nat.mul_le_mul_left f (by omega)
  omega

theorem exists_eq_two_mul_add {n : ℕ} (hn : 4 ≤ n) :
    ∃ s, n / 2 = s + 2 ∧ (n = 2 * s + 4 ∨ n = 2 * s + 5) :=
  ⟨n / 2 - 2, by omega, by omega⟩

theorem factorization_two_lt_and {f : ℕ} (hf : 1 ≤ f) :
    f.factorization 2 < f ∧ (Even f → 2 * f.factorization 2 ≤ f) := by
  refine ⟨Nat.factorization_lt 2 (by omega), ?_⟩
  rintro ⟨a, rfl⟩
  have ha : a ≠ 0 := by omega
  have h1 : (a + a).factorization 2 = 1 + a.factorization 2 := by
    rw [← two_mul, Nat.factorization_mul two_ne_zero ha, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
  have h2 : a.factorization 2 < a := Nat.factorization_lt 2 ha
  omega

theorem mul_le_add_of_mul_sub_le {f X Y v : ℕ} (hYX : Y ≤ X) (h : f * (X - Y) ≤ v) :
    f * X ≤ v + f * Y := by
  have h1 : f * X = f * (X - Y) + f * Y := by rw [← mul_add, Nat.sub_add_cancel hYX]
  omega

end Arith

section Pairs

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_four_mul_factorization_card_fixedSubgroup (hn : 4 ≤ n) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {θ : MulAut (projectiveSL n K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    f * ((n - 1) * (n - n % 2)) ≤ 4 * (Nat.card (fixedSubgroup θ)).factorization 2 := by
  obtain ⟨s, hs, hn'⟩ := exists_eq_two_mul_add hn
  rcases involution_types hn (by omega) hK hθ hθ1 with ⟨y, hy, rfl⟩ | ⟨A, rfl⟩ | hF
  · rw [fixedSubgroup_mulAut_conj_eq]
    have h := le_two_mul_factorization_card_centralizer_projectiveSL (by omega) hK (by omega) hy
    rw [hs, show s + 2 - 1 = s + 1 by omega] at h
    rcases hn' with rfl | rfl
    · rw [show 2 * s + 4 - 1 = 2 * s + 3 by omega] at h ⊢
      rw [show (2 * s + 4) % 2 = 0 by omega, Nat.sub_zero]
      have h' := mul_le_add_of_mul_sub_le (by nlinarith) h
      nlinarith
    · rw [show 2 * s + 5 - 1 = 2 * s + 4 by omega] at h ⊢
      rw [show (2 * s + 5) % 2 = 1 by omega, show 2 * s + 5 - 1 = 2 * s + 4 by omega]
      have h' := mul_le_add_of_mul_sub_le (by nlinarith) h
      nlinarith
  · have h := le_factorization_card_fixedSubgroup_graph (by omega) (by omega) hK A hθ
    rw [hs] at h
    rcases hn' with rfl | rfl
    · rw [show 2 * s + 4 - 1 = 2 * s + 3 by omega, show (2 * s + 4) % 2 = 0 by omega,
        Nat.sub_zero]
      nlinarith
    · rw [show 2 * s + 5 - 1 = 2 * s + 4 by omega, show (2 * s + 5) % 2 = 1 by omega,
        show 2 * s + 5 - 1 = 2 * s + 4 by omega]
      nlinarith
  · have h := le_four_mul_factorization_of_fieldTypeCore (by omega) hf hF
    refine le_trans (Nat.mul_le_mul_left f ?_) h
    rw [mul_comm n]
    exact Nat.mul_le_mul_left _ (Nat.sub_le n _)

omit [CharP K 2] in
theorem factorization_add_le_of_mul_dvd {θ₁ θ₂ : MulAut (projectiveSL n K)} {M : ℕ}
    (hM : M ≠ 0) (h : Nat.card (fixedSubgroup θ₁) * Nat.card (fixedSubgroup θ₂) ∣ M) :
    (Nat.card (fixedSubgroup θ₁)).factorization 2 + (Nat.card (fixedSubgroup θ₂)).factorization 2
      ≤ M.factorization 2 := by
  have h1 := factorization_two_le_of_dvd h hM
  rwa [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h1

theorem false_of_inner_pair (hn : 4 ≤ n) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {θ₂ : MulAut (projectiveSL n K)} (hθ₂ : θ₂ * θ₂ = 1) (hθ₂1 : θ₂ ≠ 1)
    {y : projectiveSL n K} (hy : orderOf y = 2)
    (hC1 : Nat.card (fixedSubgroup (MulAut.conj y)) * Nat.card (fixedSubgroup θ₂) ∣
      2 * Nat.card (MulAut (projectiveSL n K))) : False := by
  have h3 := factorization_add_le_of_mul_dvd (mul_ne_zero two_ne_zero Nat.card_pos.ne') hC1
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at h3
  have hA := factorization_card_mulAut_projectiveSL_le (K := K) (by omega : 3 ≤ n) (by omega) hK
  have h2 := le_four_mul_factorization_card_fixedSubgroup hn hf hK hθ₂ hθ₂1
  rw [fixedSubgroup_mulAut_conj_eq] at h3
  have h1 := le_two_mul_factorization_card_centralizer_projectiveSL (by omega) hK (by omega) hy
  have hw := (factorization_two_lt_and (by omega : 1 ≤ f)).1
  obtain ⟨s, hs, hn'⟩ := exists_eq_two_mul_add hn
  rw [hs, show s + 2 - 1 = s + 1 by omega] at h1
  rcases hn' with rfl | rfl
  · rw [show 2 * s + 4 - 1 = 2 * s + 3 by omega] at h1 h2 hA
    rw [show (2 * s + 4) % 2 = 0 by omega, Nat.sub_zero] at h2
    rw [show (2 * s + 4) * (2 * s + 3) / 2 = (s + 2) * (2 * s + 3) by
      rw [show (2 * s + 4) * (2 * s + 3) = 2 * ((s + 2) * (2 * s + 3)) by ring]
      omega] at hA
    exact inner_pair_arith_even hf hw (mul_le_add_of_mul_sub_le (by nlinarith) h1) h2
      (by omega)
  · rw [show 2 * s + 5 - 1 = 2 * s + 4 by omega] at h1 h2 hA
    rw [show (2 * s + 5) % 2 = 1 by omega, show 2 * s + 5 - 1 = 2 * s + 4 by omega] at h2
    rw [show (2 * s + 5) * (2 * s + 4) / 2 = (2 * s + 5) * (s + 2) by
      rw [show (2 * s + 5) * (2 * s + 4) = 2 * ((2 * s + 5) * (s + 2)) by ring]
      omega] at hA
    exact inner_pair_arith_odd hf hw (mul_le_add_of_mul_sub_le (by nlinarith) h1) h2
      (by omega)

omit [CharP K 2] in
theorem false_of_graph_pair_even (hn : 4 ≤ n) (hne : Even n) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (hθ₁ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1)
    {θ₂ : MulAut (projectiveSL n K)}
    (h₂ : (∃ B : GL (Fin n) K, θ₂ = conjAut n K B * dualAut n K ∧ θ₂ * θ₂ = 1) ∨
      (FieldTypeCore n f K θ₂ ∧ ¬(n = 4 ∧ f = 2)))
    (hC2 : Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) *
      Nat.card (fixedSubgroup θ₂) ∣ Nat.card (MulAut (projectiveSL n K))) : False := by
  have h3 := factorization_add_le_of_mul_dvd Nat.card_pos.ne' hC2
  have hA := factorization_card_mulAut_projectiveSL_le (K := K) (by omega : 3 ≤ n) (by omega) hK
  have h1 := le_factorization_card_fixedSubgroup_graph (by omega) (by omega) hK A hθ₁
  have hw := factorization_two_lt_and (by omega : 1 ≤ f)
  obtain ⟨r, rfl⟩ := hne
  have hr : (r + r) / 2 = r := by omega
  have hN : (r + r) * (r + r - 1) / 2 = r * (2 * r - 1) := by
    rw [show (r + r) * (r + r - 1) = 2 * (r * (2 * r - 1)) by
      rw [show r + r - 1 = 2 * r - 1 by omega]; ring]
    omega
  rw [hr] at h1
  rw [hN] at hA
  have hr2 : 2 ≤ r := by omega
  have h2r : r * (2 * r - 1) + r = 2 * r ^ 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    ring
  have hsq : 2 * (f * r ^ 2) = f * (r * (2 * r - 1)) + f * r := by
    rw [← mul_add, h2r]; ring
  rcases h₂ with ⟨B, rfl, hθ₂⟩ | ⟨hF, h42⟩
  · have h2 := le_factorization_card_fixedSubgroup_graph (by omega) (by omega) hK B hθ₂
    rw [hr] at h2
    have hfr : f * 2 ≤ f * r := Nat.mul_le_mul_left f hr2
    omega
  · have h2 := le_four_mul_factorization_of_fieldTypeCore (by omega) hf hF
    have hfe := hF.1
    have hw2 := hw.2 hfe
    have hrr : (r + r) * (r + r - 1) = 2 * (r * (2 * r - 1)) := by
      rw [show r + r - 1 = 2 * r - 1 by omega]; ring
    rw [hrr] at h2
    have key : 4 * (f * r ^ 2) + 2 * (f * (r * (2 * r - 1))) ≤
        4 * (f * (r * (2 * r - 1))) + 4 + 4 * f.factorization 2 := by
      have : f * (2 * (r * (2 * r - 1))) = 2 * (f * (r * (2 * r - 1))) := by ring
      omega
    have hfr : f * r ≤ 2 + 2 * f.factorization 2 := by omega
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
    · have hf4 : 4 ≤ f := by
        rcases hfe with ⟨a, ha⟩
        omega
      omega
    · have : f * 3 ≤ f * r := Nat.mul_le_mul_left f hr3
      omega

end Pairs

@[expose] def FieldTypePairExclusion (n f : ℕ) (K : Type) [Field K] : Prop :=
  ∀ θ₁ θ₂ : MulAut (projectiveSL n K), FieldTypeCore n f K θ₁ → FieldTypeCore n f K θ₂ →
    ¬ Nat.card (perfectCore (fixedSubgroup θ₁)) * Nat.card (perfectCore (fixedSubgroup θ₂)) ∣
      Nat.card (projectiveSL n K)

@[expose] def GraphOddPairExclusion (n f : ℕ) (K : Type) [Field K] : Prop :=
  Odd n → ∀ (A : GL (Fin n) K) (θ₂ : MulAut (projectiveSL n K)),
    (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1 →
    ((∃ B : GL (Fin n) K, θ₂ = conjAut n K B * dualAut n K ∧ θ₂ * θ₂ = 1) ∨
      FieldTypeCore n f K θ₂) →
    ¬ Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) * Nat.card (fixedSubgroup θ₂) ∣
      Nat.card (MulAut (projectiveSL n K))

@[expose] def GraphFourPairExclusion (n f : ℕ) (K : Type) [Field K] : Prop :=
  n = 4 → f = 2 → ∀ (A : GL (Fin n) K) (θ₂ : MulAut (projectiveSL n K)),
    (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1 →
    FieldTypeCore n f K θ₂ →
    Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) * Nat.card (fixedSubgroup θ₂) ∣
      Nat.card (MulAut (projectiveSL n K)) →
    Nat.card (perfectCore (fixedSubgroup (conjAut n K A * dualAut n K))) *
        Nat.card (perfectCore (fixedSubgroup θ₂)) ∣ Nat.card (projectiveSL n K) → False

section Assembly

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem linearInvolutionPairExclusion_of_residuals (hn : 4 ≤ n) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hR1 : FieldTypePairExclusion n f K)
    (hR2 : GraphOddPairExclusion n f K) (hR3 : GraphFourPairExclusion n f K) :
    LinearInvolutionPairExclusion n K := by
  intro θ₁ θ₂ hθ₁ hθ₁1 hθ₂ hθ₂1 hC1 hC2 hC3
  have hf1 : 1 ≤ f := by omega
  rcases involution_types hn hf1 hK hθ₁ hθ₁1 with ⟨y, hy, rfl⟩ | ⟨A, rfl⟩ | hF₁
  · exact false_of_inner_pair hn hf hK hθ₂ hθ₂1 hy hC1
  · have hC2' := hC2 (Or.inl (conjAut_mul_dualAut_not_mem_range (by omega) A))
    rcases involution_types hn hf1 hK hθ₂ hθ₂1 with ⟨y, hy, rfl⟩ | ⟨B, rfl⟩ | hF₂
    · exact false_of_inner_pair hn hf hK hθ₁ hθ₁1 hy (by rwa [mul_comm] at hC1)
    · rcases Nat.even_or_odd n with hne | hno
      · exact false_of_graph_pair_even hn hne hf hK A hθ₁ (Or.inl ⟨B, rfl, hθ₂⟩) hC2'
      · exact hR2 hno A _ hθ₁ (Or.inl ⟨B, rfl, hθ₂⟩) hC2'
    · rcases Nat.even_or_odd n with hne | hno
      · by_cases h42 : n = 4 ∧ f = 2
        · exact hR3 h42.1 h42.2 A θ₂ hθ₁ hF₂ hC2' hC3
        · exact false_of_graph_pair_even hn hne hf hK A hθ₁ (Or.inr ⟨hF₂, h42⟩) hC2'
      · exact hR2 hno A θ₂ hθ₁ (Or.inr hF₂) hC2'
  · rcases involution_types hn hf1 hK hθ₂ hθ₂1 with ⟨y, hy, rfl⟩ | ⟨B, rfl⟩ | hF₂
    · exact false_of_inner_pair hn hf hK hθ₁ hθ₁1 hy (by rwa [mul_comm] at hC1)
    · have hC2' := hC2 (Or.inr (conjAut_mul_dualAut_not_mem_range (by omega) B))
      rw [mul_comm] at hC2' hC3
      rcases Nat.even_or_odd n with hne | hno
      · by_cases h42 : n = 4 ∧ f = 2
        · exact hR3 h42.1 h42.2 B θ₁ hθ₂ hF₁ hC2' hC3
        · exact false_of_graph_pair_even hn hne hf hK B hθ₂ (Or.inr ⟨hF₁, h42⟩) hC2'
      · exact hR2 hno B θ₁ hθ₂ (Or.inr hF₁) hC2'
    · exact hR1 θ₁ θ₂ hF₁ hF₂ hC3

end Assembly

end CFSG.SeitzReduction.LinearPilot
