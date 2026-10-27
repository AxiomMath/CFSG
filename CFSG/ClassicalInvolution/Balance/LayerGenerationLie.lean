module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.Balance.PassTwoP1

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

section Definitions

variable {G : Type} [Group G]

@[expose] def IsFaithfulFourGroupAt (E : Subgroup G) (a : G) (L : Subgroup (OddQuot a))
    (F₀ : Subgroup G) : Prop :=
  F₀ ≤ E ∧ Nat.card F₀ = 4 ∧ modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) ∧
    ∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f

@[expose] def LayerGenerationOn (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G)
    (P : Subgroup (OddQuot a) → Prop) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → P L → L ≤ memberJoin Ω a →
    ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ → OddCentralizerFree (modOdd a F₀) L

@[expose] def LayerGenerationLie (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G) : Prop :=
  LayerGenerationOn Ω E a fun L => IsOddLieComponent L

@[expose] def LayerGenerationLieBig (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G) : Prop :=
  LayerGenerationOn Ω E a fun L => IsOddLieComponentBig L

theorem LayerGenerationLie.toBig {Ω : Set (Subgroup G)} {E : Subgroup G} {a : G}
    (h : LayerGenerationLie Ω E a) : LayerGenerationLieBig Ω E a :=
  fun L hL hbig hjoin => h L hL hbig.isOddLieComponent hjoin

theorem LayerGenerationAt.layerGenerationLie {Ω : Set (Subgroup G)} {E : Subgroup G} {a : G}
    (h : LayerGenerationAt E a) : LayerGenerationLie Ω E a :=
  fun L hL hlie _ F₀ ⟨h1, h2, h3, h4⟩ => h L hL hlie F₀ h1 h2 h3 h4

end Definitions

section Providers

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {E : Subgroup G}

omit [Finite G] in
theorem modOdd_sq_eq_one {a : G} {F₀ : Subgroup G} (hE2 : ∀ x ∈ E, x * x = 1) (hF₀E : F₀ ≤ E) :
    ∀ f ∈ modOdd a F₀, f * f = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : G) ∈ F₀ := hx
  rw [← map_mul]
  have : x * x = 1 := Subtype.ext (hE2 _ (hF₀E hx'))
  rw [this, map_one]

theorem IsFaithfulFourGroupAt.oddCentralizerFree_of_model (hE2 : ∀ x ∈ E, x * x = 1)
    (hmodel : LayerGenerationModel) {a : G} (ha : a ∈ E) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) (hbig : IsOddLieComponentBig L) {F₀ : Subgroup G}
    (hF : IsFaithfulFourGroupAt E a L F₀) : OddCentralizerFree (modOdd a F₀) L := by
  obtain ⟨hF₀E, h4, hFn, hfaith⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  exact OddCentralizerFree.of_le_layers
    (hmodel (OddQuot a) L hL hbig (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) (modOdd_sq_eq_one hE2 hF₀E) hFn hfaith)

theorem IsFaithfulFourGroupAt.oddCentralizerFree_of_centralizedGenerated
    (hE2 : ∀ x ∈ E, x * x = 1) {𝒜 : Set (Subgroup G)} (h𝒜 : ∀ K ∈ 𝒜, IsInvolutionMember K) {a : G}
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) (hlie : IsOddLieComponent L)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt E a L F₀)
    (hgen : CentralizedGeneratedAt 𝒜 a F₀ L) : OddCentralizerFree (modOdd a F₀) L := by
  obtain ⟨hF₀E, h4, hFn, hfaith⟩ := hF
  have hB := involutionCentralizerB_of_isOddLieComponent
    ((CFSG.isComponent_iff_open L).mp hL).2.2 hlie
  exact OddCentralizerFree.of_members l2PrimeBalance hL
    (fun f hf hf1 => hB f hf1 (modOdd_sq_eq_one hE2 hF₀E f hf) (hFn hf))
    (hgen.oddCentralizerFreeMembers h𝒜)

end Providers

section FrameProviders

variable {F : Type*} [Field F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

theorem IsFaithfulFourGroupAt.oddCentralizerFree_of_frameGenerated (Fr : WeakPreFrame F Ω E S)
    {a : G} (ha : a ∈ E) {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L)
    (hlie : IsOddLieComponent L) {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt E a L F₀)
    (hgen : FrameGeneratedAt E S a L) : OddCentralizerFree (modOdd a F₀) L := by
  have := Fr.finite
  have h4 : 4 ≤ Nat.card F := by have := Fr.five; omega
  refine hF.oddCentralizerFree_of_centralizedGenerated Fr.elem (𝒜 := S) (fun K hK => ?_) hL hlie
    (hgen.centralizedGeneratedAt_weak Fr ha hF.1 hF.2.1)
  obtain ⟨z, -, hz⟩ := Fr.exists_weakMember hK
  exact IsInvolutionMember.of_weakMember hz h4

theorem LayerGenerationLieBig.of_model (hE2 : ∀ x ∈ E, x * x = 1) (hmodel : LayerGenerationModel)
    {a : G} (ha : a ∈ E) : LayerGenerationLieBig Ω E a :=
  fun _ hL hbig _ _ hF => hF.oddCentralizerFree_of_model hE2 hmodel ha hL hbig

theorem LayerGenerationLie.of_centralizedGenerated (hE2 : ∀ x ∈ E, x * x = 1)
    {𝒜 : Set (Subgroup G)} (h𝒜 : ∀ K ∈ 𝒜, IsInvolutionMember K) {a : G}
    (hgen : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ →
        CentralizedGeneratedAt 𝒜 a F₀ L) :
    LayerGenerationLie Ω E a :=
  fun L hL hlie hjoin F₀ hF =>
    hF.oddCentralizerFree_of_centralizedGenerated hE2 h𝒜 hL hlie (hgen L hL hlie hjoin F₀ hF)

theorem LayerGenerationLie.of_frameGenerated (Fr : WeakPreFrame F Ω E S) {a : G} (ha : a ∈ E)
    (hgen : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      L ≤ memberJoin Ω a → (∃ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀) →
        FrameGeneratedAt E S a L) :
    LayerGenerationLie Ω E a :=
  fun L hL hlie hjoin F₀ hF =>
    hF.oddCentralizerFree_of_frameGenerated Fr ha hL hlie (hgen L hL hlie hjoin ⟨F₀, hF⟩)

theorem LayerGenerationLie.of_cases (Fr : WeakPreFrame F Ω E S) {a : G} (ha : a ∈ E)
    (hcase : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ →
        FrameGeneratedAt E S a L ∨
          L ≤ ⨆ f ∈ modOdd a F₀, ⨆ (_ : f ≠ 1), centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  intro L hL hlie hjoin F₀ hF
  rcases hcase L hL hlie hjoin F₀ hF with h | h
  · exact hF.oddCentralizerFree_of_frameGenerated Fr ha hL hlie h
  · exact OddCentralizerFree.of_le_layers h

end FrameProviders

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

omit [Finite G] in
theorem componentLayersAt_of_layerGenerationOn {a : G} {P : Subgroup (OddQuot a) → Prop}
    (htri : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P L ∧ L ≤ memberJoin Ω a))
    (hlay : LayerGenerationOn Ω E a P) : ComponentLayersAt Ω E a := by
  intro L hL
  rcases htri L hL with h | h | ⟨hP, hjoin⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr fun F₀ hF₀E h4 hFn hfaith =>
      hlay L hL hP hjoin F₀ ⟨hF₀E, h4, hFn, hfaith⟩)

theorem deltaCore_eq_bot_of_layerGenerationOn [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    {P : ∀ a : G, Subgroup (OddQuot a) → Prop}
    (htri : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P a L ∧ L ≤ memberJoin Ω a))
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationOn Ω E a (P a)) :
    ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥ :=
  deltaCore_eq_bot_of_weakFrame_of_layers Fr h16
    (fun a ha ha1 => componentLayersAt_of_layerGenerationOn (htri a ha ha1) (hlay a ha ha1))
    (componentClassificationOddCore_eq_bot_of_simple hnab) hGen

theorem isQuasisimple_of_layerGenerationOn [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    {P : ∀ a : G, Subgroup (OddQuot a) → Prop}
    (htri : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P a L ∧ L ≤ memberJoin Ω a))
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationOn Ω E a (P a)) {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) :
    CFSG.Open.IsQuasisimple L₀ := by
  obtain ⟨z₀, hz₀E, hz₀⟩ := Fr.toWeakPreFrame.exists_weakMember hL₀
  have hc := hz₀.isCentralInvolution
  have hΔ := deltaCore_eq_bot_of_layerGenerationOn hnab Fr h16 hGen htri hlay
  refine isQuasisimple_of_weakFrame_central Fr.toWeakPreFrame h16 hΔ hL₀ hz₀ ?_
  intro f₀ hf₀ hf₀1 M hM
  obtain ⟨hf₀E, hf₀c⟩ := mem_axisSub_iff.mp hf₀
  exact hB_of_localLieSystems hp2 h0 hA1 hΩ hIH (Fr.subset hL₀) hc
    (not_subset_center_of_ne_one hnab hf₀1)
    (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hf₀c l hl))
    (Fr.comm hz₀E hf₀E) M hM

theorem exactMembers_of_layerGenerationOn [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    {P : ∀ a : G, Subgroup (OddQuot a) → Prop}
    (htri : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P a L ∧ L ≤ memberJoin Ω a))
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationOn Ω E a (P a)) : ExactMembers Ω := by
  obtain ⟨L₀, hL₀, -⟩ := Fr.toWeakPreFrame.exists_ne
  exact exactMembers_of_weakFrame Fr.toWeakPreFrame hp2 hf h9 hΩ hsingle hL₀
    (isQuasisimple_of_layerGenerationOn hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen htri hlay hL₀)

theorem localOddCentral_of_layerGenerationOn [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    {P : ∀ a : G, Subgroup (OddQuot a) → Prop}
    (htri : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P a L ∧ L ≤ memberJoin Ω a))
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationOn Ω E a (P a)) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hmeet : FrameMeetsAt Ω E S x) : LocalOddCentral Ω {x} := by
  have hΔ := deltaCore_eq_bot_of_layerGenerationOn hnab Fr h16 hGen htri hlay
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
      obtain ⟨L₀, hL₀S, hxax, hcc⟩ := hmeet K hK
      exact Subtype.ext (member_commutes_oddCore hnab hp2 h0 hA1 hΩ hIH Fr.toWeakPreFrame h16 hΔ
        hxE hx1 hK hL₀S hxax hcc d hd k (Subgroup.mem_subgroupOf.mp hk)).symm
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

theorem stage2_of_layerGenerationOn [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    {P : ∀ a : G, Subgroup (OddQuot a) → Prop}
    (htri : ∀ a ∈ E, a ≠ 1 → ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P a L ∧ L ≤ memberJoin Ω a))
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationOn Ω E a (P a)) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  ⟨exactMembers_of_layerGenerationOn hnab hp2 hf h9 h0 fundamentalWholeA1 hΩ hsingle hIH Fr h16
      hGen htri hlay,
    fun _ ⟨hxE, hx1, hmeet⟩ =>
      localOddCentral_of_layerGenerationOn hnab hp2 h0 fundamentalWholeA1 hΩ hIH Fr h16 hGen htri
        hlay hxE hx1 hmeet⟩

theorem stage2_of_layerGenerationLie [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationLie Ω E a) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  stage2_of_layerGenerationOn (P := fun _ L => IsOddLieComponent L) hnab hp2 hf h9 h0 hΩ hsingle hIH
    Fr h16 hGen
    (fun _ _ ha1 _ hL =>
      omegaFreeAt_or_rankOneAt_or_isOddLieComponent_le_join hp2 h0 fundamentalWholeA1 hΩ hIH
        (not_subset_center_of_ne_one hnab ha1) hL)
    hlay

theorem stage2_of_layerGenerationLieBig [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hF3 : ∀ a ∈ E, a ≠ 1 → NoComponentOverF3 p f Ω a)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationLieBig Ω E a) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  stage2_of_layerGenerationOn (P := fun _ L => IsOddLieComponentBig L) hnab hp2 hf h9 h0 hΩ hsingle
    hIH Fr h16 hGen
    (fun a ha ha1 _ hL =>
      omegaFreeAt_or_rankOneAt_or_isOddLieComponentBig hp2 h0 fundamentalWholeA1 hq hΩ hIH
        (not_subset_center_of_ne_one hnab ha1) (hF3 a ha ha1) hL)
    hlay

end Chain

end CFSG.ClassicalInvolution.Balance
