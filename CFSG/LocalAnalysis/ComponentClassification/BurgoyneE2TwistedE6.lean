module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit


@[expose] def BurgoyneE2TwistedE6Input : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 2 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), orderOf α = 2 →
          BurgCoreFor α ∨ BurgTorusFor α

theorem burgoynePropA_twistedE6_of_twisted (hT : BurgoyneE2TwistedE6Input) {X : Type} [Group X]
    [Finite X] (hX : IsM4 X) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .twistedE6 n p f) {t : X}
    (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -⟩ := hX
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨hp, hf, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf hU
    exact propAConclusion_of_rows hsimple hnab (exceptional_fixed_center_trivial TwistTag.E6 K σ) e
      (hT p f hp hp2 hf K hK σ hσ) ht hY hYO
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
