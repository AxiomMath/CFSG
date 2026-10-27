module

public import CFSG.ClassicalInvolution.Balance.BootstrapInvolutory
public import CFSG.ClassicalInvolution.Balance.BootstrapLevi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime]

@[expose] def FrameNoF3 (p f : ℕ) [Fact p.Prime] : Prop :=
  p ^ f = 27 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        ∀ A : Subgroup G, MemberFamily p f (CoreAssembly.conjClass K) A
          (frameFamily p f (CoreAssembly.conjClass K) A) →
        ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a

theorem bootTriple_of_involutoryModel_final (hmodel : LayerGenerationInvolutoryModel)
    (hMF1 : FrameMF1 p f) (hcover : FrameCoverage p f) (hexotic : ExoticLeviBlock p f)
    (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hF3' : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a :=
    fun a ha ha1 => by
      by_cases h27 : p ^ f = 27
      · exact hF3 h27 G hnab K z hz hBelow hconn A hM a ha ha1
      · exact NoComponentOverF3.of_ne_27 a hq h27
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_of_layers_exotic hnab hp2
    hq hΩ (CoreAssembly.exists_single_class K) hIH (omegaConnected_of_deltaConnected hconn) hM
    (hMF1 G hnab K z hz hBelow hconn A hM) (hcover G hnab K z hz hBelow hconn A hM)
    (componentLayersAt_of_involutoryModel_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ hIH hM
      hmodel hF3')
    (fun a ha hfa => by
      obtain ⟨K', -, hK'⟩ := hfa
      exact centralizerGenerationModOTwo_of_involutoryModel_of_noF3 hp2 hq
        ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM ha
        (not_subset_center_of_ne_one hnab hK'.ne_one) (hF3' a ha hK'.ne_one))
    hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_model_final (hmodel : LayerGenerationModel) (hMF1 : FrameMF1 p f)
    (hcover : FrameCoverage p f) (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) :
    CoreAssembly.BootTriple p f :=
  bootTriple_of_involutoryModel_final (layerGenerationInvolutoryModel_of_model hmodel) hMF1 hcover
    hexotic hF3

end CFSG.ClassicalInvolution.Balance.Bootstrap
