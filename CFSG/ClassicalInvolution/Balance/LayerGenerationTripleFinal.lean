module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTripleBoot
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem deltaCore_eq_bot_and_localOddCentral_of_frameFamily' [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) (hInv : TwoClassInvolutionsConj p)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a) :
    (∀ F ∈ CFSG.Open.signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧
      ∃ K₀ ∈ frameFamily p f Ω A, ∃ z₀ ∈ A, IsClassicalMember p f K₀ z₀ ∧
        K₀ ≤ Subgroup.centralizer (A : Set G) ∧ LocalOddCentral Ω {z₀} := by
  have h0 := ModelFacts.modelClauseZero
  have hA1 := fundamentalWholeA1
  have hlink : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      InvolutionLink p f Ω A (frameFamily p f Ω A) a := by
    intro a ha hfa
    obtain ⟨K, hK𝒦, hK⟩ := hfa
    refine involutionLink_of_inCommonComponent' hΩ hp2 hq hIH hInv
      (not_subset_center_of_ne_one hnab hK.ne_one) hM.subset (fun K hK => ?_) ?_
    · obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
      exact ⟨z, hzA, hz⟩
    · intro M hMa
      obtain ⟨L, hL𝒦, hcc⟩ := hcover a ha ⟨K, hK𝒦, hK⟩ M hMa
      obtain ⟨-, -, -, hLA⟩ := hM.involution L hL𝒦
      exact ⟨L, hL𝒦, hLA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)), hcc⟩
  have hgen := generation_of_memberFamily_of_closure hΩ hM hconn hgenModO hlink
  have hRB : RankThreeBalance A :=
    ⟨hM.elem, hM.card, weakBalanced_of_memberFamily hnab hp2 hq h0 hA1 hΩ hIH hM,
      twoBalancedWrt_of_memberFamily_of_layers hM hloc⟩
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hRB
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, hz₀A, hz₀, hK₀A⟩ := hM.involution K₀ hK₀
  refine ⟨hΔ, K₀, hK₀, z₀, hz₀A, hz₀, hK₀A,
    localOddCentral_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH hM.elem hM.card hΔ hz₀A
      hz₀.ne_one fun K hK => ?_⟩
  obtain ⟨L, hL𝒦, hcc⟩ := hcover z₀ hz₀A ⟨K₀, hK₀, hz₀⟩ K hK
  obtain ⟨hLΩ, hLA, z, hzA, hz⟩ := hL𝒦
  exact ⟨L, hLΩ, z, hzA, hz, hLA, hcc⟩

theorem exactMembers_and_localOddCentral_of_frameFamily_of_layers_exotic' [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) (hInv : TwoClassInvolutionsConj p)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨hΔ, K₀, hK₀, z₀, hz₀A, hz₀, hK₀A, hP1⟩ :=
    deltaCore_eq_bot_and_localOddCentral_of_frameFamily' hnab hp2 hq hΩ hIH hconn hM hInv hcover
      hloc hgenModO
  have hK₀Ω : K₀ ∈ Ω := hM.subset hK₀
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle hK₀Ω hz₀ hP1
  refine ⟨?_, hP1all⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic
  · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two A hM.elem (by rw [hM.card]; norm_num)
    exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hsingle hIH hK₀Ω hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hM.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)

end Frame

section BootTriple

variable {p f : ℕ} [Fact p.Prime]

theorem bootTriple_of_triple_final' (hmodel : LayerGenerationTriple)
    (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f) (hexotic : ExoticLeviBlock p f)
    (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hT, hM⟩ := exists_indepTripleOn hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hF3' : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a :=
    fun a ha ha1 => by
      by_cases h27 : p ^ f = 27
      · exact hF3 h27 G hnab K z hz hBelow hconn A hM a ha ha1
      · exact NoComponentOverF3.of_ne_27 a hq h27
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_of_layers_exotic' hnab hp2
    hq hΩ (CoreAssembly.exists_single_class K) hIH (omegaConnected_of_deltaConnected hconn) hM
    (twoClassInvolutionsConj p) (hcover hp2 hq G hnab K z hz hBelow hconn A hM)
    (componentLayersAt_of_triple_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ hIH hT hmodel
      hF3')
    (fun a ha hfa => by
      obtain ⟨K', -, hK'⟩ := hfa
      exact centralizerGenerationModOTwo_of_triple_of_noF3 hp2 hq
        ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM hT ha
        (not_subset_center_of_ne_one hnab hK'.ne_one) (hF3' a ha hK'.ne_one))
    hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_model_final' (hmodel : LayerGenerationModel)
    (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f) (hexotic : ExoticLeviBlock p f)
    (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_triple_final' (layerGenerationTriple_of_model hmodel) hcover hexotic hF3

end BootTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
