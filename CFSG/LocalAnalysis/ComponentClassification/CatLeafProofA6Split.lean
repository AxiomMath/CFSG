module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OddLieA6CentreFor (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible τ n p f →
    Blueprint.LieModel S τ n p f → ∀ α : MulAut S, orderOf α = 2 →
      A6CentreForm (fixedSubgroup α)

theorem oddLieA6ComponentCentre_of_families (h : ∀ τ, OddLieA6CentreFor τ) :
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      Blueprint.OddLieType S → ∀ α : MulAut S, orderOf α = 2 →
      ∀ K : Subgroup (FixedCommutingProduct.fixedSubgroup α), IsComponent K →
        Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 6)) → IsPGroup 2 ↥(center ↥K) :=
  fun S _ _ _ _ ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ α hα K hK hA =>
    h τ S n p f hp hp2 hadm hm α hα K hK hA

theorem oddLieA6CentreFor_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n p f : ℕ, p ≠ 2 → ¬ StatedLieAdmissible τ n p f) : OddLieA6CentreFor τ :=
  fun _ _ n p f _ hp2 hadm => absurd hadm (hτ n p f hp2)

theorem oddLieA6CentreFor_twistedB2 : OddLieA6CentreFor .twistedB2 :=
  oddLieA6CentreFor_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem oddLieA6CentreFor_twistedF4 : OddLieA6CentreFor .twistedF4 :=
  oddLieA6CentreFor_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem oddLieA6CentreFor_Tits : OddLieA6CentreFor .Tits :=
  oddLieA6CentreFor_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

end CFSG.ComponentClassification.CatLeafProof
