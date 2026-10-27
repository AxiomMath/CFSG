module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem linear_two_automorphism_semilinear_isomorphism (K : Type) [Field K] [Finite K] :
    ∃ c : coordinateE K ≃* MulAut (coordinateG K),
      (∀ (e : coordinateE K) (g : coordinateG K),
        ((c e g : coordinateG K) : Equiv.Perm (Omega K)) =
          (e : Equiv.Perm (Omega K)) * (g : Equiv.Perm (Omega K)) *
            (e : Equiv.Perm (Omega K))⁻¹) ∧
      (∀ g : coordinateG K,
        c ⟨g, ((coordinateG_le_D K).trans (coordinateD_le_E K)) g.property⟩ = MulAut.conj g) ∧
      ∀ α : MulAut (coordinateG K), ∃! e : coordinateE K,
        ∀ g : coordinateG K, ((α g : coordinateG K) : Equiv.Perm (Omega K)) =
          (e : Equiv.Perm (Omega K)) * (g : Equiv.Perm (Omega K)) *
            (e : Equiv.Perm (Omega K))⁻¹ := by
  refine ⟨coordinateConjugationEquiv K, coordinateConjugation_apply_coe K,
    coordinateConjugation_on_G K, fun α => ?_⟩
  obtain ⟨e, he⟩ := (coordinateConjugationEquiv K).surjective α
  refine ⟨e, fun g => ?_, fun e' he' => ?_⟩
  · rw [← he]
    exact coordinateConjugation_apply_coe K e g
  · refine (coordinateConjugationEquiv K).injective (MulEquiv.ext fun g => Subtype.ext ?_)
    rw [he]
    exact (coordinateConjugation_apply_coe K e' g).trans (he' g).symm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
