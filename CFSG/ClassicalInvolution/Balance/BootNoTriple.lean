module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleBasic
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.QNineStage
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic.CoreAssembly
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rankThreeBalance_of_bootData [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) {L₀ : Subgroup G} {z₀ : G}
    (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (hbad : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → A ≠ Subgroup.closure ({z₀, a, b} : Set G) →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b)
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hfree : ∀ b ∈ A, b ≠ 1 → ∀ L : Subgroup (OddQuot b), CFSG.IsComponent L →
      (OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) → LargeCentralizerOn A b L) :
    RankThreeBalance A :=
  ⟨hA, hcard,
    weakBalanced_of_pairs hnab hp2 hq CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A hbad,
    twoBalancedWrt_of_member_of_layers hA hL₀Ω hz₀ hz₀A hL₀A hloc
      fun a ha ha1 _ hF₀A hF₀4 _ L hL hLF =>
        exists_mem_ne_one_centralizes_of_large hA hcard (hfree a ha ha1 L hL hLF) hF₀A hF₀4⟩

theorem stage2_of_balanced_bootData [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {S : Set (Subgroup G)}
    (hF : FrameSideTwo p f Ω A S) (hconn : OmegaConnected Ω) :
    (∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) ∧
      ∀ x : G, x ≠ 1 → (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
        InCommonComponent x K (conjSub g L₀)) → LocalOddCentral Ω {x} := by
  have hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤ :=
    rankTwoSpan_eq_top hΩ hF hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hA
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  exact ⟨hΔ, fun x hx1 hcov => localOddCentral_of_conj_data hnab hp2 hq
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hA.elem hA.card
    hΔ hL₀Ω hz₀ hz₀A hL₀A hx1 hcov⟩

theorem layers_of_kg8 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hmodel : LayerGenerationModel) :
    ∀ b ∈ A, b ≠ 1 → ComponentLayersAt Ω A b :=
  componentLayersAt_of_model hnab hp2 hq h27 CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    hΩ hIH (fun x hx => by rw [← pow_two]; exact hA.2 x hx) hmodel

theorem inCommonComponent_self [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {a : G} (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : K ∈ centMembers Ω a) : InCommonComponent a K K := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH
    (not_subset_center_of_ne_one hnab ha1)
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨K, hK, rfl⟩ : modOdd a K ∈ memberImages Ω a)
  exact ⟨D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hi⟩

theorem cover_of_involution [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A) {a : G} (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : K ∈ centMembers Ω a) (hKa : IsClassicalMember p f K a) :
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀) := by
  obtain ⟨K₀, -, hall⟩ := hsingle
  obtain ⟨g₁, hg₁⟩ := hall K hK.1
  obtain ⟨g₀, hg₀⟩ := hall L₀ hL₀Ω
  have hKL : K = conjSub (g₁ * g₀⁻¹) L₀ := by
    rw [conjSub_mul, hg₀, conjSub_inv_conjSub]
    exact hg₁
  refine ⟨g₁ * g₀⁻¹, ?_, hKL ▸ inCommonComponent_self hnab hp2 hΩ hIH ha1 hK⟩
  have hcl := hz₀.conj (g₁ * g₀⁻¹)
  rw [← hKL] at hcl
  have := hKa.eq_of_isCentralInvolution hp2 (pos_of_five_le hq) hcl.isCentralInvolution
  rw [← this]
  exact conj_mem_conjSub hz₀A

theorem exactMembers_and_localOddCentral_of_balanced [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : OmegaConnected Ω) {A : Subgroup G} (hA : RankThreeBalance A) {L₀ : Subgroup G}
    {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {S : Set (Subgroup G)}
    (hF : FrameSideTwo p f Ω A S) {a : G} (ha1 : a ≠ 1)
    (haClassical : ∃ M ∈ Ω, IsClassicalMember p f M a)
    (hcover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
      ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀))
    (hnine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
      InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hf : 0 < f := pos_of_five_le hq
  obtain ⟨hΔ, hP1⟩ := stage2_of_balanced_bootData hnab hp2 hq hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A hF
    hconn
  have hP1a : LocalOddCentral Ω {a} := by
    refine hP1 a ha1 fun K hK => ?_
    by_cases hKa : IsClassicalMember p f K a
    · exact cover_of_involution hnab hp2 hq hΩ hsingle hIH hL₀Ω hz₀ hz₀A ha1 hK hKa
    · exact hcover K hK hKa
  refine ⟨?_, ?_⟩
  · by_cases h9 : p ^ f = 9
    · obtain ⟨x, -, hx1, hcov, hlevi⟩ := hnine h9
      exact exactMembers_of_localLeviComponent hp2 hq hΩ hsingle (hP1 x hx1 hcov) hlevi
    · obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
        Nat.prime_two A hA.elem (by rw [hA.card]; norm_num)
      exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9
        CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hsingle hIH
        hL₀Ω hz₀ (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA.elem hF₀.1)
        (hL₀A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  · obtain ⟨M, hMΩ, hM⟩ := haClassical
    exact localOddCentral_of_classicalMember hp2 hf hΩ hsingle hMΩ hM hP1a

structure GoodBootData (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  z₀A : z₀ ∈ A
  cent : L₀ ≤ Subgroup.centralizer (A : Set G)
  badPairs : ∀ b ∈ A, b ≠ 1 → ∀ c ∈ A, c ≠ 1 → A ≠ Subgroup.closure ({z₀, b, c} : Set G) →
    ⁅involutionOddCore b ⊓ Subgroup.centralizer {c}, A⁆ ≤ involutionOddCore c
  frame : FrameSideTwo p f Ω A S
  free : ∀ b ∈ A, b ≠ 1 → ∀ L : Subgroup (OddQuot b), CFSG.IsComponent L →
    (OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) → LargeCentralizerOn A b L
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

theorem exactMembers_and_localOddCentral_of_good [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : OmegaConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G}
    {S : Set (Subgroup G)} {a : G} (h : GoodBootData p f Ω L₀ z₀ A S a)
    (hloc : ∀ b ∈ A, b ≠ 1 → ComponentLayersAt Ω A b) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} :=
  exactMembers_and_localOddCentral_of_balanced hnab hp2 hq hΩ hsingle hIH hconn
    (rankThreeBalance_of_bootData hnab hp2 hq hΩ hIH h.elem h.card h.mem h.cls h.z₀A h.cent
      h.badPairs hloc h.free)
    h.mem h.cls h.z₀A h.cent h.frame h.a1 h.aClassical h.cover h.nine

omit [Finite G] in
theorem omegaConnected_of_routeD {Ω : Set (Subgroup G)}
    (h : CFSG.ClassicalInvolution.RouteD.DeltaConnected Ω) : OmegaConnected Ω := by
  classical
  intro L hL L' hL'
  have hreach := h.preconnected ⟨L, hL⟩ ⟨L', hL'⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ v : Ω, Relation.ReflTransGen (CFSG.ClassicalInvolution.Models.commGraph Ω).Adj
      ⟨L, hL⟩ v → Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) L
        (v : Subgroup G) := by
    intro v hv
    induction hv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨-, hcomm⟩ := (CFSG.ClassicalInvolution.Models.commGraph_adj).mp hbc
      exact ih.tail ⟨c.2, hcomm⟩
  exact key ⟨L', hL'⟩ hreach

@[expose] def GoodBootDataExists (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        GoodBootData p f (CoreAssembly.conjClass K) L₀ z₀ A S a

theorem bootNoTriple_of_goodBootData (h27 : p ^ f ≠ 27) (hmodel : LayerGenerationModel)
    (h : GoodBootDataExists p f) : BootNoTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hgood⟩ := h G hnab hp2 hq K z hz hBelow hconn hdata hT
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_good hnab hp2 hq hΩ
    (exists_single_class K) hIH (omegaConnected_of_routeD hconn) hgood
    (layers_of_kg8 hnab hp2 hq h27 hΩ hIH hgood.elem hmodel)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

end CFSG.ClassicalInvolution.Balance.BootRank3
