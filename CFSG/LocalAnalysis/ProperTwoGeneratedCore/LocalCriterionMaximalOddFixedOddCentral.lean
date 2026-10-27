module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII

variable {K Ω : Type*} [Group K] [MulAction K Ω]

theorem two_pretransitive_class_pair_flips [Nonempty Ω]
    (htwo : MulAction.IsMultiplyPretransitive K Ω 2) (s : K)
    (hno : ∀ a : Ω, s • a ≠ a) :
    ∀ a b : Ω, a ≠ b → ∃ r ∈ involutionPointClass s, r • a = b := by
  let x : Ω := Classical.choice inferInstance
  intro a b hab
  obtain ⟨n, hna, hnb⟩ := (MulAction.is_two_pretransitive_iff.mp htwo)
    (Ne.symm (hno x)) hab
  refine ⟨n * s * n⁻¹, ⟨n⁻¹, ?_⟩, ?_⟩
  · simp only [rightConjugateElem, inv_inv]
  · rw [← hna, mul_smul, mul_smul, inv_smul_smul]
    exact hnb

theorem two_pretransitive_odd_central_fixed_free_card_le_two
    [Finite K] [Finite Ω]
    (htwo : MulAction.IsMultiplyPretransitive K Ω 2)
    (J : Subgroup K) [J.Normal] (hJodd : Odd (Nat.card J))
    (s : K) (hs : orderOf s = 2)
    (hcentral : QuotientGroup.mk' J s ∈ Subgroup.center (K ⧸ J))
    (hno : ∀ a : Ω, s • a ≠ a) : Nat.card Ω ≤ 2 := by
  classical
  by_cases hempty : IsEmpty Ω
  · let := hempty
    simp
  have : Nonempty Ω := not_isEmpty_iff.mp hempty
  apply odd_central_involution_class_pair_flips_card_le_two J hJodd s hs hcentral
  · rintro r ⟨n, rfl⟩ a hf
    apply hno (n • a)
    have hh := congrArg (fun y : Ω => n • y) hf
    simpa only [rightConjugateElem, mul_smul, smul_inv_smul] using hh
  · exact two_pretransitive_class_pair_flips htwo s hno

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed
