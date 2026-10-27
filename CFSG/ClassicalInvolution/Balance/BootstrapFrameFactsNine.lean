module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTripleNine
public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsG2

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exactMembers_and_localOddCentral_of_frameFamily_nine' [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationModel) (hconn : OmegaConnected Ω)
    {A : Subgroup G} (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hInv : TwoClassInvolutionsConj p)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hnine : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → p ^ f = 9 →
      LocalLeviComponent p f Ω a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h0 := ModelFacts.modelClauseZero
  have hA1 := fundamentalWholeA1
  have hloc := componentLayersAt_of_model hnab hp2 hq h27 h0 hΩ hIH
    (fun x hx => by
      rw [← pow_two]
      exact hM.elem.2 x hx) hmodel
  have hgenModO : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a →
      CentralizerGenerationModOTwo Ω A a := fun a ha hfa =>
    centralizerGenerationModOTwo_of_memberFamily hp2 hq h27 h0 hA1 hΩ hIH hmodel hM ha
      (by
        obtain ⟨K, -, hK⟩ := hfa
        exact not_subset_center_of_ne_one hnab hK.ne_one)
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
  have hP1 : LocalOddCentral Ω {z₀} :=
    localOddCentral_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH hM.elem hM.card hΔ hz₀A
      hz₀.ne_one fun K hK => by
        obtain ⟨L, hL𝒦, hcc⟩ := hcover z₀ hz₀A ⟨K₀, hK₀, hz₀⟩ K hK
        obtain ⟨hLΩ, hLA, z, hzA, hz⟩ := hL𝒦
        exact ⟨L, hLΩ, z, hzA, hz, hLA, hcc⟩
  refine ⟨?_, localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hM.subset hK₀) hz₀ hP1⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_localLeviComponent hp2 hq hΩ hsingle hP1
      (hnine z₀ hz₀A ⟨K₀, hK₀, hz₀⟩ h9)
  · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two A hM.elem (by rw [hM.card]; norm_num)
    exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 h0 hA1 hΩ hsingle hIH
      (hM.subset hK₀) hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hM.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)

theorem bootTriple_of_model_nine' (h27 : p ^ f ≠ 27) (hmodel : LayerGenerationModel)
    (hInv : TwoClassInvolutionsConj p) (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f)
    (hlevi : FrameLevi p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_nine' hnab hp2 hq h27 hΩ
    (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hmodel
    (omegaConnected_of_deltaConnected hconn) hM hInv
    (hcover hp2 hq G hnab K z hz hBelow hconn A hM)
    (hlevi G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_model_nine_of_trialityD4 (h27 : p ^ f ≠ 27) (hmodel : LayerGenerationModel)
    (hD4 : TrialityD4InvolutionsConj p) (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f)
    (hlevi : FrameLevi p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_model_nine' h27 hmodel (twoClassInvolutionsConj_of_trialityD4 hD4) hcover hlevi

end CFSG.ClassicalInvolution.Balance.Bootstrap
