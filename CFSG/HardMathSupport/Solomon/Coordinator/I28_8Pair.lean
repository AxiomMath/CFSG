module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

theorem twoSeven_of_th1 (h : Th1Factorization) : Th1FactorizationTwoSeven := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ R S hRs hRp hO hSR hS2 hSidx D _ ρ Q hQ hSQ hinv hRQ
  have h3 : ¬ 3 ∣ Nat.card R := fun hd => by
    rcases hRp 3 Nat.prime_three hd with h | h <;> omega
  have h5 : ¬ 5 ∣ Nat.card R := fun hd => by
    rcases hRp 5 (by norm_num) hd with h | h <;> omega
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have hSfin : Finite (S.map ρ) := ((Set.toFinite (S : Set G)).image ρ).to_subtype
  set H : Fin 3 → Subgroup D := fun i =>
    (Subgroup.normalizer (tripleOf S i : Set G) ⊓ R).map ρ with hH
  have hSH : ∀ i, S.map ρ ≤ H i := fun i =>
    Subgroup.map_mono (le_inf (Subgroup.le_normalizer.trans
      (Sec7.normalizer_le_normalizer_tripleOf S i)) hSR)
  have hHle : ∀ i, H i ≤ S.map ρ ⊔ Q := fun i => hRQ ▸ Subgroup.map_mono inf_le_right
  have hHS : ∀ i, ¬ Q ≤ H i → H i ≤ S.map ρ := by
    intro i hQi x hx
    have hxSQ := hHle i hx
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (S.map ρ) Q hSQ
    have hxm : x ∈ (↑(S.map ρ) : Set D) * ↑Q := hmul ▸ hxSQ
    obtain ⟨s, hs, q, hq, rfl⟩ := hxm
    have hqH : q ∈ H i := by
      have := mul_mem (Subgroup.inv_mem _ (hSH i hs)) hx
      simpa using this
    by_cases hq1 : q = 1
    · show s * q ∈ _
      rw [hq1, mul_one]; exact hs
    · exfalso
      apply hQi
      have hord : orderOf q ∣ 7 := by
        have := Subgroup.orderOf_dvd_natCard Q hq
        rwa [hQ] at this
      have h7 : orderOf q = 7 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hord with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hq1
        · exact h
      have hz : Subgroup.zpowers q = Q := by
        apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hq)
        rw [Nat.card_zpowers, h7, hQ]
      rw [← hz]
      exact (Subgroup.zpowers_le).2 hqH
  refine ⟨Finset.univ.filter (fun i => Q ≤ H i), ?_, fun i hi => (Finset.mem_filter.1 hi).2⟩
  by_contra hlt
  push Not at hlt
  have hc : 2 ≤ (Finset.univ.filter (fun i => Q ≤ H i))ᶜ.card := by
    rw [Finset.card_compl]; simp only [Fintype.card_fin]; omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hc
  have hi' : ¬ Q ≤ H i := by simpa using hi
  have hj' : ¬ Q ≤ H j := by simpa using hj
  have hfac := h G R S hRs h3 h5 hO hSR hS2 hSidx i j hij
  have hQS : Q ≤ S.map ρ := by
    intro q hq
    have hqR : q ∈ R.map ρ := hRQ ▸ Subgroup.mem_sup_right hq
    obtain ⟨r, hr, rfl⟩ := hqR
    have hr' : r ∈ ((Subgroup.normalizer (tripleOf S i : Set G) ⊓ R : Subgroup G) : Set G) *
        ((Subgroup.normalizer (tripleOf S j : Set G) ⊓ R : Subgroup G) : Set G) := hfac ▸ hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr'
    rw [map_mul]
    exact mul_mem (hHS i hi' ⟨a, ha, rfl⟩) (hHS j hj' ⟨b, hb, rfl⟩)
  have hdvd : Nat.card Q ∣ Nat.card (S.map ρ) := Subgroup.card_dvd_of_le hQS
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 (hS2.map ρ)
  rw [hQ, hn] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) hdvd
  omega

theorem input28_8_of_th1 (h : Th1Factorization) :
    Input28_8 :=
  input28_8_of_twoSeven (twoSeven_of_th1 h)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
