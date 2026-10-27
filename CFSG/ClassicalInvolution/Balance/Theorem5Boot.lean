module

public import CFSG.ClassicalInvolution.Balance.Theorem5Triangle
public import CFSG.ClassicalInvolution.Balance.BootstrapFinal
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section P1

theorem localOddCentral_of_framesMeet [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {x : G} (hx1 : x ≠ 1)
    (hmeet : ∀ K ∈ centMembers Ω x, ∃ A : Subgroup G, IsElemAbelian 2 A ∧ Nat.card A = 8 ∧
      (∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) ∧ x ∈ A ∧ ∃ L₀ ∈ Ω, ∃ z₀ ∈ A,
        IsClassicalMember p f L₀ z₀ ∧ L₀ ≤ Subgroup.centralizer (A : Set G) ∧
          InCommonComponent x K L₀) :
    LocalOddCentral Ω {x} := by
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centMembers Ω x).Nonempty
  · have hgen := (inClass_local hΩ {x} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer Ω {x})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨K, hK, hKY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨A, hA, hcard, hΔ, hxA, L₀, hL₀Ω, z₀, hz₀A, hz₀, hL₀A, hcc⟩ := hmeet K hK
      exact Subtype.ext (member_commutes_oddCore_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH
        hA hcard hΔ hxA hx1 hK hL₀Ω hz₀ hz₀A hL₀A hcc d hd k
        (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) :=
      hgen ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer Ω x = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ z : ↥(centLayer Ω x), z = 1 := fun z =>
      Subtype.ext (by
        have := z.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

end P1

section Assembly

@[expose] def FramesMeetAt (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (𝒯 : Set (Subgroup G))
    (x : G) : Prop :=
  ∀ K ∈ centMembers Ω x, ∃ A ∈ 𝒯, x ∈ A ∧ ∃ L ∈ frameFamily p f Ω A, InCommonComponent x K L

@[expose] def TriangleFramesMeetAt (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) :
    Prop :=
  FramesMeetAt p f Ω (triangleFrames p f Ω) x

section P1Frames

theorem localOddCentral_of_alphaCore_eq_bot [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {A F₀ : Subgroup G}
    (hB : RankThreeBalance A) (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A) (hα : alphaCore F₀ = ⊥)
    {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hmeet : ∀ K ∈ centMembers Ω x, ∃ L ∈ frameFamily p f Ω A, InCommonComponent x K L) :
    LocalOddCentral Ω {x} :=
  localOddCentral_of_framesMeet hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH
    hx1 fun K hK => by
      obtain ⟨L, ⟨hLΩ, hLA, z, hzA, hz⟩, hcc⟩ := hmeet K hK
      exact ⟨A, hB.elem, hB.card, deltaCore_eq_bot_of_alphaCore_eq_bot hB hF₀ hα, hxA, L, hLΩ, z,
        hzA, hz, hLA, hcc⟩

theorem localOddCentral_of_connectedBalancedFrames [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A')
    {x : G} (hx1 : x ≠ 1) (hmeet : FramesMeetAt p f Ω 𝒯 x) : LocalOddCentral Ω {x} := by
  have hΔ := deltaCore_eq_bot_of_connected_frames
    (componentClassificationOddCore_eq_bot_of_simple hnab) hinv hbal hcon
  exact localOddCentral_of_framesMeet hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1 hΩ
    hIH hx1 fun K hK => by
      obtain ⟨A, hA, hxA, L, ⟨hLΩ, hLA, z, hzA, hz⟩, hcc⟩ := hmeet K hK
      exact ⟨A, (hbal A hA).elem, (hbal A hA).card, hΔ A hA, hxA, L, hLΩ, z, hzA, hz, hLA, hcc⟩

end P1Frames

theorem exactMembers_and_localOddCentral_of_balancedFrames [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A')
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ 𝒯)
    (hcov : ∃ K₀ ∈ frameFamily p f Ω A₀, ∃ z₀ ∈ A₀, IsClassicalMember p f K₀ z₀ ∧
      FramesMeetAt p f Ω 𝒯 z₀)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΔ := deltaCore_eq_bot_of_connected_frames
    (componentClassificationOddCore_eq_bot_of_simple hnab) hinv hbal hcon
  have hB₀ := hbal A₀ hA₀
  obtain ⟨K₀, hK₀, z₀, hz₀A, hz₀, hmeet⟩ := hcov
  have hK₀Ω : K₀ ∈ Ω := hK₀.1
  have hK₀A : K₀ ≤ Subgroup.centralizer (A₀ : Set G) := hK₀.2.1
  have hP1 : LocalOddCentral Ω {z₀} :=
    localOddCentral_of_connectedBalancedFrames hnab hp2 hq hΩ hIH hbal hinv hcon hz₀.ne_one hmeet
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle hK₀Ω hz₀ hP1
  refine ⟨?_, hP1all⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic
  · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two A₀ hB₀.elem (by rw [hB₀.card]; norm_num)
    exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hsingle hIH hK₀Ω hz₀
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB₀.elem hF₀.1)
      (hK₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ A₀ hA₀ F₀ hF₀)

theorem exactMembers_and_localOddCentral_of_rankTwoSpan [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hconn : OmegaConnected Ω) {A₀ : Subgroup G}
    (hB : RankThreeBalance A₀) (htop : rankTwoSpan A₀ = ⊤)
    (hcov : ∃ K₀ ∈ frameFamily p f Ω A₀, ∃ z₀ ∈ A₀, IsClassicalMember p f K₀ z₀ ∧
      FramesMeetAt p f Ω (frameConjugates A₀) z₀)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balancedFrames hnab hp2 hq hΩ hsingle hIH hconn
    (rankThreeBalance_of_mem_frameConjugates hB) (frameConjugates_inv A₀)
    (connected_conjClass_of_rankTwoSpan_eq_top htop) (A₀ := A₀) ⟨1, by ext y; simp⟩ hcov hexotic

theorem exactMembers_and_localOddCentral_of_connectedFrames [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hconn : OmegaConnected Ω)
    (hF3 : ∀ A, IndepTripleOn p f Ω A → ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a)
    {𝒯 : Set (Subgroup G)} (hsub : 𝒯 ⊆ triangleFrames p f Ω)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A')
    {A₀ : Subgroup G} (hA₀ : A₀ ∈ 𝒯)
    (hcov : ∃ K₀ ∈ frameFamily p f Ω A₀, ∃ z₀ ∈ A₀, IsClassicalMember p f K₀ z₀ ∧
      FramesMeetAt p f Ω 𝒯 z₀)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  exact exactMembers_and_localOddCentral_of_balancedFrames hnab hp2 hq hΩ hsingle hIH hconn
    (fun A hA => rankThreeBalance_of_indepTripleOn hnab hp2 hf hq hΩ hIH hmodel (hsub hA)
      (hF3 A (hsub hA))) hinv hcon hA₀ hcov hexotic

theorem exactMembers_and_localOddCentral_of_triangleConnected [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hconn : OmegaConnected Ω)
    (hF3 : ∀ A, IndepTripleOn p f Ω A → ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a)
    (htri : TriangleConnected p f Ω) {A₀ : Subgroup G} (hA₀ : IndepTripleOn p f Ω A₀)
    (hcov : ∃ K₀ ∈ frameFamily p f Ω A₀, ∃ z₀ ∈ A₀, IsClassicalMember p f K₀ z₀ ∧
      TriangleFramesMeetAt p f Ω z₀)
    (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_connectedFrames hnab hp2 hq hΩ hsingle hIH hmodel hconn hF3
    (𝒯 := triangleFrames p f Ω) (fun _ h => h)
    (fun _ hA g => indepTripleOn_map hΩ.conjInvariant hA g) htri hA₀ hcov hexotic

end Assembly

section BootTriple

@[expose] def ConnectedBalancedFramesExist (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∃ 𝒯 : Set (Subgroup G), (∀ A ∈ 𝒯, RankThreeBalance A) ∧
          (∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) ∧
          (∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
            Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') ∧
          ∃ A₀ ∈ 𝒯, ∃ K₀ ∈ frameFamily p f (CoreAssembly.conjClass K) A₀, ∃ z₀ ∈ A₀,
            IsClassicalMember p f K₀ z₀ ∧ FramesMeetAt p f (CoreAssembly.conjClass K) 𝒯 z₀

@[expose] def ConnectedFramesExist (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∃ 𝒯 : Set (Subgroup G), 𝒯 ⊆ triangleFrames p f (CoreAssembly.conjClass K) ∧
          (∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) ∧
          (∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
            Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') ∧
          ∃ A₀ ∈ 𝒯, ∃ K₀ ∈ frameFamily p f (CoreAssembly.conjClass K) A₀, ∃ z₀ ∈ A₀,
            IsClassicalMember p f K₀ z₀ ∧ FramesMeetAt p f (CoreAssembly.conjClass K) 𝒯 z₀

@[expose] def TriangleConnectedAll (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        TriangleConnected p f (CoreAssembly.conjClass K)

@[expose] def CoveredTriangleExists (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∃ A₀ : Subgroup G, IndepTripleOn p f (CoreAssembly.conjClass K) A₀ ∧
          ∃ K₀ ∈ frameFamily p f (CoreAssembly.conjClass K) A₀, ∃ z₀ ∈ A₀,
            IsClassicalMember p f K₀ z₀ ∧
              TriangleFramesMeetAt p f (CoreAssembly.conjClass K) z₀

theorem connectedFramesExist_of_triangle (htri : TriangleConnectedAll p f)
    (hcov : CoveredTriangleExists p f) : ConnectedFramesExist p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  obtain ⟨A₀, hA₀, hcov'⟩ := hcov G hnab hp2 hq K z hz hBelow hconn hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact ⟨triangleFrames p f (CoreAssembly.conjClass K), fun _ h => h,
    fun _ hA g => indepTripleOn_map hΩ.conjInvariant hA g, htri G hnab hp2 hq K z hz hBelow hconn,
    A₀, hA₀, hcov'⟩

@[expose] def TriangleLayers (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        ∀ A : Subgroup G, IndepTripleOn p f (CoreAssembly.conjClass K) A →
          ∀ a ∈ A, a ≠ 1 → ComponentLayersAt (CoreAssembly.conjClass K) A a

theorem noComponentOverF3_of_frameNoF3 [IsSimpleGroup G] (hF3 : FrameNoF3 p f)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hconn : RouteD.DeltaConnected (CoreAssembly.conjClass K)) {A : Subgroup G}
    (hA : IndepTripleOn p f (CoreAssembly.conjClass K) A) :
    ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a := fun a ha ha1 => by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  by_cases h27 : p ^ f = 27
  · exact hF3 h27 G hnab K z hz hBelow hconn A (memberFamily_of_indepTripleOn hp2 hf hA) a ha
      ha1
  · exact NoComponentOverF3.of_ne_27 a hq h27

theorem triangleLayers_of_involutoryModel (hmodel : LayerGenerationInvolutoryModel)
    (hF3 : FrameNoF3 p f) : TriangleLayers p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact componentLayersAt_of_involutoryModel_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) (memberFamily_of_indepTripleOn hp2 hf hA) hmodel
    (noComponentOverF3_of_frameNoF3 hF3 hnab hp2 hq hz hBelow hconn hA)

theorem triangleLayers_of_triple (hmodel : LayerGenerationTriple) (hF3 : FrameNoF3 p f) :
    TriangleLayers p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact componentLayersAt_of_triple_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) hA hmodel
    (noComponentOverF3_of_frameNoF3 hF3 hnab hp2 hq hz hBelow hconn hA)

theorem connectedBalancedFramesExist_of_layers (hlay : TriangleLayers p f)
    (hfam : ConnectedFramesExist p f) : ConnectedBalancedFramesExist p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨𝒯, hsub, hinv, hcon, hcov⟩ := hfam G hnab hp2 hq K z hz hBelow hconn hind
  exact ⟨𝒯, fun A hA => rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH
    (hsub hA) (hlay G hnab hp2 hq K z hz hBelow hconn A (hsub hA)), hinv, hcon, hcov⟩

theorem bootTriple_of_balancedFrames (hfam : ConnectedBalancedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨𝒯, hbal, hinv, hcon, A₀, hA₀, hcov⟩ := hfam G hnab hp2 hq K z hz hBelow hconn hind
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_balancedFrames hnab hp2 hq hΩ
    (CoreAssembly.exists_single_class K) hIH (omegaConnected_of_deltaConnected hconn) hbal hinv
    hcon hA₀ hcov hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_triangleLayers (hlay : TriangleLayers p f)
    (hfam : ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  bootTriple_of_balancedFrames (connectedBalancedFramesExist_of_layers hlay hfam) hexotic

theorem bootTriple_of_triple_frames (hmodel : LayerGenerationTriple)
    (hfam : ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) :
    CoreAssembly.BootTriple p f :=
  bootTriple_of_triangleLayers (triangleLayers_of_triple hmodel hF3) hfam hexotic

theorem bootTriple_of_model_frames (hmodel : LayerGenerationModel)
    (hfam : ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) :
    CoreAssembly.BootTriple p f :=
  bootTriple_of_triple_frames (layerGenerationTriple_of_model hmodel) hfam hexotic hF3

theorem bootTriple_of_involutoryModel_frames (hmodel : LayerGenerationInvolutoryModel)
    (hfam : ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) :
    CoreAssembly.BootTriple p f :=
  bootTriple_of_triangleLayers (triangleLayers_of_involutoryModel hmodel hF3) hfam hexotic

theorem bootTriple_of_model_triangle (hmodel : LayerGenerationModel)
    (htri : TriangleConnectedAll p f) (hcov : CoveredTriangleExists p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_model_frames hmodel (connectedFramesExist_of_triangle htri hcov) hexotic hF3

theorem bootTriple_of_involutoryModel_triangle (hmodel : LayerGenerationInvolutoryModel)
    (htri : TriangleConnectedAll p f) (hcov : CoveredTriangleExists p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_involutoryModel_frames hmodel (connectedFramesExist_of_triangle htri hcov) hexotic
    hF3

end BootTriple

end CFSG.ClassicalInvolution.Balance.Theorem5
