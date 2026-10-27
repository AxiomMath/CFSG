module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticField
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Model

variable {r : ℕ} {K : Type} [Field K]

theorem conj_injective_statedSp [NeZero r] [CharP K 2] :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := proj_surjective x
  obtain ⟨h, rfl⟩ := proj_surjective y
  rw [← spInner_eq_conj, ← spInner_eq_conj] at hxy
  rw [spInner_injective hxy]

theorem oddCore_statedSp_inf_centralizer_eq_bot {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hIH : inner (StatedProj (StatedSp r K)) ≤ H) {α : MulAut (StatedProj (StatedSp r K))}
    (hαH : α ∈ H) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ centralizer ({α} : Set (MulAut (StatedProj (StatedSp r K))))) = ⊥ := by
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  by_cases hαI : α ∈ inner (StatedProj (StatedSp r K))
  · exact even_symplectic_inner_involution_full_centralizer_odd_core (by omega) hf hK H hIH hαI hα
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hE := (automorphism_generation (K := K) hr).1
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut
    (show α ∈ spSemilinearAutGroup r K by rw [hE]; exact mem_top α)
  have hφ : φ ≠ 1 := (spInner_mul_fieldAut_not_mem_inner_iff g φ).1 (hgφ ▸ hαI)
  have haa : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  obtain ⟨hfe, hφσ, -⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) hf hK haa g φ hgφ hφ
  exact (even_symplectic_field_centralizers_and_intermediate_odd_cores (r := r) (by omega)
    (by obtain ⟨m, hm⟩ := hfe; omega) hfe hK φ hφσ).2.2.2.2.2 H hIH
    (by rw [hE]; exact le_top) α hαH hα hαI

theorem involutionCriterion_spInner_of_criteria [NeZero r] [CharP K 2]
    (hne : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s))
    (heq : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s = (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s))
    {α : MulAut (StatedProj (StatedSp r K))} (hαI : α ∈ inner (StatedProj (StatedSp r K)))
    (hα : orderOf α = 2) : InvolutionCriterion α := by
  rw [← range_spInner] at hαI
  obtain ⟨s, rfl⟩ := hαI
  have hsord : orderOf s = 2 := by rw [← orderOf_injective _ spInner_injective s, hα]
  have hs : s * s = 1 := by rw [← sq, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    exact absurd hsord (by norm_num)
  by_cases hW : displacement s = (pairedSympForm K r).orthogonal (displacement s)
  · exact heq s hs hs1 hW
  · exact hne s hs hs1 hW

theorem involutionCriterion_statedSp {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hne : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s))
    (heq : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s = (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s))
    {x : MulAut (StatedProj (StatedSp r K))} (hx : orderOf x = 2) : InvolutionCriterion x := by
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero r := ⟨by omega⟩
  by_cases hxI : x ∈ inner (StatedProj (StatedSp r K))
  · exact involutionCriterion_spInner_of_criteria hne heq hxI hx
  · exact involutionCriterion_sp_of_not_mem_inner hr hK (by rw [← sq, ← hx, pow_orderOf_eq_one])
      hxI

theorem hypothesisOne_statedSp {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hne : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s))
    (heq : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s = (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s)) :
    HypothesisOne (StatedProj (StatedSp r K)) := by
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero r := ⟨by omega⟩
  exact hypothesisOne_of_involutionCriterion conj_injective_statedSp
    (fun H hIH _ hαH hα => oddCore_statedSp_inf_centralizer_eq_bot hr hK H hIH hαH hα)
    (fun _ hx => involutionCriterion_statedSp hr hK hne heq hx)

end Model

theorem hypothesisOne_of_lieModel_PSp {Y : Type} [Group Y] {r f : ℕ} (hr : 3 ≤ r)
    (hne : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
        displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
        InvolutionCriterion (spInner r K s))
    (heq : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
        displacement s = (pairedSympForm K r).orthogonal (displacement s) →
        InvolutionCriterion (spInner r K s))
    (h : CFSG.Blueprint.LieModel Y .PSp r 2 f) : HypothesisOne Y := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two
      (one_le_of_nontrivial_of_natCard_eq_two_pow hK) hK
    exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm
      (hypothesisOne_statedSp hr hK (hne K hK) (heq K hK))
  · simp [CFSG.Blueprint.chevalleyExceptionalTags] at ht
  · simp [CFSG.Blueprint.reeTitsTags] at ht
  · cases ht

end CFSG.SeitzReduction
