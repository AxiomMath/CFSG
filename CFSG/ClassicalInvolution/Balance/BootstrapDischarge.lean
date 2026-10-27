module

public import CFSG.ClassicalInvolution.Balance.BootstrapStage2Alpha
public import CFSG.ClassicalInvolution.Balance.LayerGenerationLie

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem componentLayersAt_of_model [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x * x = 1) (hmodel : LayerGenerationModel) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (NoComponentOverF3.of_ne_27 a hq h27) hL)
    (LayerGenerationLieBig.of_model hA2 hmodel ha)

theorem stage2_of_exactTriple_of_model [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω)
    (hΩ₃ : K₃ ∈ Ω) (hz₁ : IsClassicalMember p f K₁ z₁) (hz₂ : IsClassicalMember p f K₂ z₂)
    (hz₃ : IsClassicalMember p f K₃ z₃) (hmodel : LayerGenerationModel)
    (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      CentralizerGenerationModOTwo Ω T.group a)
    (hlink : ∀ a ∈ T.group, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      InvolutionLink p f Ω T.group ({K₁, K₂, K₃} : Set (Subgroup G)) a) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.group, deltaCore F = ⊥) ∧
      Stage2 Ω {x | x ∈ T.group ∧ x ≠ 1 ∧ TripleMeetsAt Ω K₁ K₂ K₃ x} :=
  stage2_of_exactTriple_of_layers_wb hnab hp2 hq h9 h0 fundamentalWholeA1 hΩ hsingle hIH T hind
    hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃
    (componentLayersAt_of_model hnab hp2 hq h27 h0 hΩ hIH (fun x hx => by
      rw [← pow_two]
      exact T.isElemAbelian.2 x hx) hmodel)
    hconn hgenModO hlink

end CFSG.ClassicalInvolution.Balance.Bootstrap
