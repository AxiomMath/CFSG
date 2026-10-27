module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem one_le_of_nontrivial_of_natCard_eq_two_pow {α : Type*} [Nontrivial α] {f : ℕ}
    (h : Nat.card α = 2 ^ f) : 1 ≤ f := by
  have : Finite α := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have h1 := Finite.one_lt_card (α := α)
    rw [h, pow_zero] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact hf

theorem isPerfect_statedSp_of_three_le {r : ℕ} {k : Type} [Field k] [Finite k] (hr : 3 ≤ r) :
    Group.IsPerfect (StatedSp r k) := by
  have : Fintype k := Fintype.ofFinite k
  refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp r k ?_
  have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
  rcases Nat.lt_or_ge (Nat.card k) 4 with h4 | h4
  · interval_cases Nat.card k
    · exact .inr (.inr ⟨rfl, hr⟩)
    · exact .inr (.inl ⟨rfl, by omega⟩)
  · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset k).card by
        rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
    exact .inl ⟨s, hs⟩

section Field

variable {r : ℕ} {K : Type} [Field K]

theorem fieldAut_proj_subfieldSpHom (σ : K ≃+* K) (g : StatedSp r (descentField σ)) :
    fieldAut r K σ (proj r K (subfieldSpHom r (descentField σ) g)) =
      proj r K (subfieldSpHom r (descentField σ) g) := by
  rw [fieldAut_proj, fieldSp_subfieldSpHom]

theorem involutionCriterion_spFieldAut {f : ℕ} (hr : 3 ≤ r) (hf : 2 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2)) :
    InvolutionCriterion (fieldAut r K σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, hcentN, -⟩ := even_symplectic_field_centralizers_and_intermediate_odd_cores
    (r := r) (by omega) hf hfe hK σ hσ
  obtain ⟨hσσ, -, -⟩ := mem_zpowers_of_forall_fixed hf hfe hK hσ
  have : Group.IsPerfect (StatedSp r (descentField σ)) := isPerfect_statedSp_of_three_le hr
  have := Group.IsPerfect.range ((proj r K).comp (subfieldSpHom r (descentField σ)))
  have hfix : ∀ n ∈ ((proj r K).comp (subfieldSpHom r (descentField σ))).range,
      fieldAut r K σ n = n := by
    rintro _ ⟨g, rfl⟩
    exact fieldAut_proj_subfieldSpHom σ g
  have hx2 : fieldAut r K σ ^ 2 = 1 := by rw [sq, ← map_mul, hσσ, map_one]
  refine involutionCriterion_of_le_zpowers hx2
    (le_closure_odd_fixed_of_perfect hfix Subgroup.commutator_eq_self) fun β _ hβ => ?_
  rw [← hcentN]
  refine mem_inf.2 ⟨by rw [(automorphism_generation hr).1]; exact mem_top β,
    mem_centralizer_iff.2 ?_⟩
  rintro _ ⟨g, rfl⟩
  change spInner r K (subfieldSpHom r (descentField σ) g) * β =
    β * spInner r K (subfieldSpHom r (descentField σ) g)
  rw [spInner_eq_conj]
  exact conj_mul_eq_mul_conj_of_apply_eq (hβ _ ⟨g, rfl⟩)

theorem involutionCriterion_sp_of_not_mem_inner {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a * a = 1)
    (haI : a ∉ inner (StatedProj (StatedSp r K))) : InvolutionCriterion a := by
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut
    (show a ∈ spSemilinearAutGroup r K by rw [(automorphism_generation hr).1]; exact mem_top a)
  have hφ : φ ≠ 1 := (spInner_mul_fieldAut_not_mem_inner_iff g φ).1 haI
  obtain ⟨hfe, hφσ, -, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) hf hK ha g φ rfl hφ
  rw [hh]
  exact (involutionCriterion_spFieldAut hr (by obtain ⟨m, hm⟩ := hfe; omega) hfe hK φ hφσ).conj _

end Field

end CFSG.SeitzReduction
