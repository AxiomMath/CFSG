module

public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module QuadraticForm CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Odd

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem orth3_mem_orthDerived_of_pow_prime (Q : QuadraticForm K W)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W)
    (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : W ≃ₗ[K] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) :
    g ∈ orthDerived Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (orderOf g) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hgp)
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨-, -, -, -, -, -, hoddΩ, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    exact hoddΩ g hg hodd
  · rcases Nat.even_or_odd (Nat.card K) with hev | hod
    ·
      have hchar : CharP K 2 := by
        have := Fintype.ofFinite K
        refine ringChar.of_eq ?_
        rw [FiniteField.even_card_iff_char_two]
        rw [← Nat.card_eq_fintype_card]
        exact Nat.even_iff.mp hev
      obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
          Q hQ
      by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, Q u = 0
      ·
        obtain ⟨U, hUn, hUQ⟩ := hS
        have hn2 : n = 2 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le Q hUQ (by omega))
        subst hn2
        have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨
              finrank K W = 5)) ∨
            (Odd (Nat.card K) ∧ finrank K W = 6 ∧
              ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
            (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :=
          Or.inr (Or.inr ⟨by omega, U, hUn, hUQ⟩)
        obtain ⟨-, h2, -⟩ :=
          orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase
        have hnexc : ¬ ((finrank K W = 3 ∧ Nat.card K = 3) ∨
            ((finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
              (Nat.card K = 2 ∨ Nat.card K = 3))) := by
          rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
        obtain ⟨-, hP, -⟩ := h2 hnexc
        by_cases hg1 : g = 1
        · rw [hg1]; exact one_mem _
        · have hord : orderOf (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = p := by
            rw [← Subgroup.orderOf_coe]
            exact orderOf_eq_prime hgp hg1
          have := mem_of_isPGroup_two_of_orderOf_prime hP hp hp2 hord
          have h4 := Subgroup.mem_map_of_mem
            (TauCeti.QuadraticMap.orthogonalGroup Q).subtype this
          rwa [Subgroup.map_subtype_commutator] at h4
      · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0 := by
          intro U hU
          by_contra hcon
          push Not at hcon
          exact hS ⟨U, hU, hcon⟩
        rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
        · exfalso
          refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
          · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
              (by simp)
          · intro u hu
            obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
            simpa using hb x 0
        ·
          have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
              Q u = 0 := by
            intro u hu
            obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
            simpa using hb x 0 0 0
          have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
              b (Sum.inl i))) = n - 1 :=
            (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
              (by simp)
          have hn23 : n = 2 ∨ n = 3 := by
            by_contra hne
            exact hT (exists_threeSingular_of_le Q hU (by omega))
          have hd46 : finrank K W = 4 ∨ finrank K W = 6 := by omega
          have hts' : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, Q u ≠ 0 :=
            fun U hU => hts U (by omega)
          obtain ⟨-, -, -, -, hoddJ, -⟩ :=
            even_minus_four_six_actual_derived_extraction Q hQ hd46 hts'
          exact hoddJ g hg hodd
    ·
      have hdim6 : finrank K W ≤ 6 :=
        (finite_odd_quadratic_low_Witt_dimension_bound hod Q hQ).2.2 hT
      have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨
            finrank K W = 5)) ∨
          (Odd (Nat.card K) ∧ finrank K W = 6 ∧
            ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
          (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
        by_cases hd6 : finrank K W = 6
        · exact Or.inr (Or.inl ⟨hod, hd6, hT⟩)
        · exact Or.inl ⟨hod, by omega⟩
      obtain ⟨-, h2, -⟩ :=
        orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase
      have hnexc : ¬ ((finrank K W = 3 ∧ Nat.card K = 3) ∨
          ((finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
            (Nat.card K = 2 ∨ Nat.card K = 3))) := by
        rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
      obtain ⟨-, hP, -⟩ := h2 hnexc
      by_cases hg1 : g = 1
      · rw [hg1]; exact one_mem _
      · have hord : orderOf (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = p := by
          rw [← Subgroup.orderOf_coe]
          exact orderOf_eq_prime hgp hg1
        have := mem_of_isPGroup_two_of_orderOf_prime hP hp hp2 hord
        have h4 := Subgroup.mem_map_of_mem
          (TauCeti.QuadraticMap.orthogonalGroup Q).subtype this
        rwa [Subgroup.map_subtype_commutator] at h4

end Odd

section Fixed

open Polynomial CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orth3_mem_supportedFixedDerived (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (h3 : 3 ≤ finrank K (fixedSpace x)) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x (X - 1)) (hgp : g ^ p = 1) :
    g ∈ supportedFixedDerived Q x := by
  refine mem_supportedFixedDerived.mpr ⟨hg, ?_⟩
  refine orth3_mem_orthDerived_of_pow_prime (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate h3 hK4 hp hp2
    (restrictFixed_mem_orthogonalGroup ⟨g, hg⟩) ?_
  have h1 : (restrictFixed Q x ⟨g, hg⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext hgp
    rw [this, map_one]
  exact h1

end Fixed

end CFSG.HardMathSupport.Timmesfeld.CrossChar
