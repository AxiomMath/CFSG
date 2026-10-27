module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameCore
public import CFSG.ClassicalInvolution.Balance.BootstrapBootTripleNine
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem generation_of_involutoryModel (hmodel : LayerGenerationInvolutoryModel)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (hAY : A ≤ centLayer Ω a)
    (D : LieDecomposition (memberImages Ω a) (memberJoin Ω a)) (i : D.ι)
    (hbig : IsOddLieComponentBig (D.Q i)) {F' : Subgroup G} (hF' : F' ∈ signalizerFunctorEk 2 2 A)
    (hfaith : ∀ x ∈ modOdd a F', x ≠ 1 → ¬ ∀ y ∈ D.Q i, x * y = y * x) :
    D.Q i ≤ ⨆ g ∈ modOdd a F', ⨆ (_ : g ≠ 1),
      memberJoin Ω a ⊓ Subgroup.centralizer ({g} : Set (OddQuot a)) := by
  have hF'A : F' ≤ A := hF'.1
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hM.elem.2 x hx
  have hF'2 : ∀ x ∈ F', x * x = 1 := fun x hx => hA2 x (hF'A hx)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
  have hFb4 : Nat.card (modOdd a F') = 4 := by
    rw [card_modOdd_of_exponent_two (hF'A.trans hAC) hF'2, hF'.2]
    norm_num
  have hFbJ : modOdd a F' ≤ memberJoin Ω a := modOdd_le_memberJoin (hF'A.trans hAY)
  have hFbN : modOdd a F' ≤
      Subgroup.normalizer ((D.Q i : Subgroup (OddQuot a)) : Set (OddQuot a)) :=
    hFbJ.trans (le_normalizer_of_normal_subgroupOf (D.le_join i) (D.normal_subgroupOf i))
  obtain ⟨T, hTL, hT2, hT⟩ := memberFamily_exists_involution_action_modOdd hM ha D i hF'A
  exact kg8_generation_involutory hmodel (D.le_join i) (D.normal_subgroupOf i) (D.quasisimple i)
    hbig hFbJ hFb4 (modOdd_sq_eq_one hA2 hF'A) hFbN hfaith ⟨T, hTL, hT2, hT⟩

theorem centralizerGenerationModOTwo_of_involutoryModel_of_noF3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Ω a) : CentralizerGenerationModOTwo Ω A a := by
  classical
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (A : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAY : A ≤ centLayer Ω a := by
    rw [hM.generate, Subgroup.closure_le]
    rintro z ⟨K, hK, hz⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact le_centLayer ⟨hM.subset hK, hcen hKA⟩ hz.mem
  obtain ⟨D, hD⟩ := lieDecomposition_memberImages_big hp2 h0 hA1 hq hΩ hIH hnc hF3
  refine centralizerGenerationModOTwo_of_components hΩ.conjInvariant hM.elem hM.card ha ha1 hAY D
    fun i F' hF' hfaith => ?_
  rcases hD i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hbig
  · exfalso
    have hr1 : RankOneAt Ω a (D.Q i) := by
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    have hF'A : F' ≤ A := hF'.1
    have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
      rw [← pow_two]
      exact hM.elem.2 x hx
    have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, ha⟩))
    have hcard : 1 < Nat.card (modOdd a F') := by
      rw [card_modOdd_of_exponent_two (hF'A.trans hAC) fun x hx => hA2 x (hF'A hx), hF'.2]
      norm_num
    have : Nontrivial (modOdd a F') := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨x, hx1⟩ := exists_ne (1 : modOdd a F')
    obtain ⟨k, hk, hkx⟩ := mem_modOdd_iff.mp x.2
    refine hfaith x x.2 (fun h => hx1 (Subtype.ext h)) fun y hy => ?_
    rw [← hkx]
    exact oddQuotMk_centralizes_of_memberFamily hM ha (Or.inr hr1) (hF'A hk) _ y hy
  · exact generation_of_involutoryModel hmodel hM ha hAY D i hbig hF' hfaith

theorem centralizerGenerationModOTwo_of_involutoryModel (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hM : MemberFamily p f Ω A 𝒦) (ha : a ∈ A) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) :
    CentralizerGenerationModOTwo Ω A a :=
  centralizerGenerationModOTwo_of_involutoryModel_of_noF3 hp2 hq h0 hA1 hΩ hIH hmodel hM ha hnc
    (NoComponentOverF3.of_ne_27 a hq h27)

theorem componentLayersAt_of_involutoryModel_of_noF3 [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦)
    (hmodel : LayerGenerationInvolutoryModel)
    (hF3 : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a) :
    ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a := fun a ha ha1 =>
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponentBig L)
    (fun _ hL => omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ
      hIH (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1) hL)
    (LayerGenerationLieBig.of_involutoryModel hp2 h0 fundamentalWholeA1 hΩ hIH hmodel hM ha
      (not_subset_center_of_ne_one hnab ha1))

end Main

section Stage2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exactMembers_and_localOddCentral_of_frameFamily_involutory_nine [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hconn : OmegaConnected Ω) (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a)
    (hnine : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → p ^ f = 9 →
      LocalLeviComponent p f Ω a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_frameFamily_of_layers_nine hnab hp2 hq hΩ hsingle hIH hconn
    hM hMF1 hcover (componentLayersAt_of_involutoryModel hnab hp2 hq h27
      ModelFacts.modelClauseZero hΩ hIH hM hmodel)
    (fun a ha hfa => centralizerGenerationModOTwo_of_involutoryModel hp2 hq h27
      ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM ha (by
        obtain ⟨K, -, hK⟩ := hfa
        exact not_subset_center_of_ne_one hnab hK.ne_one))
    hnine

theorem exactMembers_and_localOddCentral_of_frameFamily_involutory [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h27 : p ^ f ≠ 27) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hmodel : LayerGenerationInvolutoryModel) (hconn : OmegaConnected Ω)
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_frameFamily_involutory_nine hnab hp2 hq h27 hΩ hsingle hIH
    hmodel hconn hM hMF1 hcover fun _ _ _ h => absurd h h9

end Stage2

section BootTriple

variable {p f : ℕ} [Fact p.Prime]

theorem bootTriple_of_involutoryModel (h9 : p ^ f ≠ 9) (h27 : p ^ f ≠ 27)
    (hmodel : LayerGenerationInvolutoryModel) (hMF1 : FrameMF1 p f) (hcover : FrameCoverage p f) :
    CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_involutory hnab hp2 hq h9
    h27 hΩ (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hmodel
    (omegaConnected_of_deltaConnected hconn) hM
    (hMF1 G hnab K z hz hBelow hconn A hM)
    (hcover G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_involutoryModel_nine (h27 : p ^ f ≠ 27)
    (hmodel : LayerGenerationInvolutoryModel) (hMF1 : FrameMF1 p f) (hcover : FrameCoverage p f)
    (hlevi : FrameLevi p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily_involutory_nine hnab hp2 hq
    h27 hΩ (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hmodel
    (omegaConnected_of_deltaConnected hconn) hM
    (hMF1 G hnab K z hz hBelow hconn A hM)
    (hcover G hnab K z hz hBelow hconn A hM)
    (hlevi G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end BootTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
