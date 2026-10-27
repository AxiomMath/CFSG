module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2

variable {Y : Type*} [Group Y]

theorem card_le_five_sq_of_centralizes_component {X : Type*} [Group X] [Finite X]
    {L₀ L₁ : Subgroup Y}
    (hL₀ : IsComponentOf L₀ ⊤) (hL₁ : IsComponentOf L₁ ⊤) (h01 : L₀ ≠ L₁)
    (hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₀ ∨ L = L₁)
    (hC : ∀ x ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Layer.subgroup Y : Set Y), (orderOf x).Coprime 5)
    (hout : ¬ 5 ∣ Nat.card (Outer ↥L₀)) {U : Subgroup X}
    (φ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃* ↥U) (hX : Open.pRank 5 (⊤ : Subgroup X) ≤ 2)
    {E : Subgroup Y} (hE : IsElemAbelian 5 E) (h₁ : E ≤ Subgroup.centralizer (L₁ : Set Y)) :
    Nat.card E ≤ 5 ^ 2 := by
  obtain ⟨hle, hE₁₁⟩ := card_le_mul_of_two_components hL₀ hL₁ h01 hall hC hout φ hX hE
  have hbot : E ⊓ Subgroup.centralizer (L₀ : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ E ⊓ Subgroup.centralizer (L₀ : Set Y) ⊓ Subgroup.centralizer (L₁ : Set Y) :=
      ⟨hx, h₁ hx.1⟩
    rwa [hE₁₁] at this
  rw [hbot, Subgroup.card_bot, one_mul] at hle
  exact hle

end CFSG.LocalAnalysis.RankThreeTheoremC
