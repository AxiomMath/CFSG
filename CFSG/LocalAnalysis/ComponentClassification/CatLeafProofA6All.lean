module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6ExcFam
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6OmegaFam

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup

theorem oddLieA6ComponentCentre_holds
    : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      Blueprint.OddLieType S → ∀ α : MulAut S, orderOf α = 2 →
      ∀ K : Subgroup (FixedCommutingProduct.fixedSubgroup α), IsComponent K →
        Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 6)) → IsPGroup 2 ↥(center ↥K) :=
  oddLieA6ComponentCentre_of_families fun τ => by
    cases τ
    exacts [oddLieA6CentreFor_PSL, oddLieA6CentreFor_PSU, oddLieA6CentreFor_PSp,
      oddLieA6CentreFor_POmegaOdd, oddLieA6CentreFor_POmegaPlus, oddLieA6CentreFor_POmegaMinus,
      oddLieA6CentreFor_G2, oddLieA6CentreFor_F4, oddLieA6CentreFor_E6, oddLieA6CentreFor_E7,
      oddLieA6CentreFor_E8, oddLieA6CentreFor_twistedE6, oddLieA6CentreFor_trialityD4,
      oddLieA6CentreFor_twistedB2, oddLieA6CentreFor_twistedG2, oddLieA6CentreFor_twistedF4,
      oddLieA6CentreFor_Tits]

end CFSG.ComponentClassification.CatLeafProof
