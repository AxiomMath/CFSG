module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnCross
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnMember
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyHybrid

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices MemberClass FuzzyEdgeInFrame FuzzyLinkConn
    FuzzyVertexConn FuzzyAxisExact FuzzyFrameBalance)

section Link

variable {p f : ℕ} [Fact p.Prime]

@[expose] def LinkNoF3 (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ (a : G) (M : Subgroup G), M ∈ 𝒞 K → IsClassicalMember p f M a →
          NoComponentOverF3 p f (linkFamily p f (𝒞 K) a) a

theorem LinkNoF3.of_ne_27 (𝒞 : MemberClass) (h27 : p ^ f ≠ 27) : LinkNoF3 p f 𝒞 := by
  intro G _ _ _ _ _ hq K z hz hBelow hconn hind a M hM𝒞 hM
  exact NoComponentOverF3.of_ne_27 a hq h27

end Link

section Basis

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem FrameBasis.swap {B J N : Subgroup G} {t u : G} (hb : FrameBasis p f 𝒞 a B J t N u) :
    FrameBasis p f 𝒞 a B N u J t where
  frame := hb.frame
  vertex := hb.vertex
  memJ := hb.memN
  clsJ := hb.clsN
  memN := hb.memJ
  clsN := hb.clsJ
  tB := hb.uB
  uB := hb.tB
  tqJ := hb.tqN
  tqN := hb.tqJ
  ta := hb.u_ne_a
  uni := by
    intro h
    obtain ⟨-, M, -, hM, -⟩ := hb.vertex
    have ha2 : a * a = 1 := hb.sq hb.aB
    have ha1 : a ≠ 1 := hM.isCentralInvolution.ne_one
    have hle : Subgroup.closure ({a, t} : Set G) ≤ Subgroup.closure ({a, u} : Set G) := by
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact h
    have h4t : Nat.card (Subgroup.closure ({a, t} : Set G)) = 4 :=
      card_closure_pair_eq_four ha2 (hb.sq hb.tB) ha1 hb.t_ne_one (Ne.symm hb.ta)
        (hb.comm hb.aB hb.tB)
    have h4u : Nat.card (Subgroup.closure ({a, u} : Set G)) = 4 :=
      card_closure_pair_eq_four ha2 (hb.sq hb.uB) ha1 hb.u_ne_one (Ne.symm hb.u_ne_a)
        (hb.comm hb.aB hb.uB)
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h4t, h4u])
    exact hb.uni (by rw [heq]; exact Subgroup.subset_closure (by simp))

end Basis

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem fuzzyEdgeInFrame_canonClass (hF3 : LinkNoF3 p f (canonClass p f)) :
    FuzzyEdgeInFrame p f (canonClass p f) (tqAdj p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind M hM𝒞 N hN𝒞 zM zN hM hN hE hne
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  obtain ⟨a', u', hM', -, -, hNa'⟩ := hE
  have ha' : a' = zM := hM.eq_of_isCentralInvolution hp2 hf hM'.isCentralInvolution
  have haN : zM ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (ha' ▸ hNa')
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkData hnab hp2 hq hBelow hinv hM𝒞 hM
    (hF3 G hnab hp2 hq K z hz hBelow hconn hind zM M hM𝒞 hM)
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
    ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
  have hA₀ := fuzzyFrameOn_canonClass_of_indepTripleOn hAex
  obtain ⟨z₀, hz₀⟩ := Theorem5.FuzzyFrameOn.exists_vertex hA₀
  have hz₀' := hz₀
  obtain ⟨-, J₀, hJ₀𝒞, hJ₀, -⟩ := hz₀'
  obtain ⟨h, hh⟩ := exists_conj_of_mem_canonClass hp2 hf hJ₀𝒞 hJ₀ hM𝒞 hM
  have hA₁ := Theorem5.FuzzyFrameOn.map hinv hA₀ h
  have haA₁ := Theorem5.mem_fuzzyVertices_map hinv hz₀ h
  rw [hh] at haA₁
  obtain ⟨J, t, N₁, u₁, hb⟩ := exists_frameBasis hA₁ haA₁
  have ha2 : zM * zM = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨c₁, hc₁⟩ := ld.sec.exists_comp ld.D hb.linkN
  obtain ⟨c₀, hc₀⟩ := ld.sec.exists_comp ld.D (triangleResidual_mem_linkFamily hN𝒞 hN haN)
  by_cases h0J : c₀ = cJ
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp ld hp2 hinv hb hN𝒞 hN haN (j := cJ) hcJ
      (by rw [← h0J]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases h0N : c₀ = c₁
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp ld hp2 hinv hb.swap hN𝒞 hN haN (j := c₁)
      hc₁ (by rw [← h0N]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases hcl : SameClass zM t zN
  · have hcl' : ¬ SameClass zM u₁ zN := fun h => hb.not_sameClass (hcl.trans ha2 (h.symm ha2))
    obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross ld hp2 hq hinv hcan hM𝒞 hM hb.memN hb.clsN
      (hb.tqN hb.aB) hb.u_ne_a hN𝒞 hN haN hua (j₁ := c₁) (j₂ := c₀) (Ne.symm h0N) hc₁ hc₀ hcl'
    exact ⟨B, hB, haB, huB⟩
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross ld hp2 hq hinv hcan hM𝒞 hM hb.memJ hb.clsJ
      (hb.tqJ hb.aB) hb.ta hN𝒞 hN haN hua (j₁ := cJ) (j₂ := c₀) (Ne.symm h0J) hcJ hc₀ hcl
    exact ⟨B, hB, haB, huB⟩

theorem fuzzyVertexConn_canonClass_of_linkNoF3 (hF3 : LinkNoF3 p f (canonClass p f)) :
    FuzzyVertexConn p f (canonClass p f) :=
  fuzzyVertexConn_canonClass (fuzzyEdgeInFrame_canonClass hF3)

theorem fuzzyLinkConn_canonClass (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hF3 : LinkNoF3 p f (canonClass p f)) : FuzzyLinkConn p f (canonClass p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' haA haA'
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haA0 := haA
  obtain ⟨-, M, hM𝒞, hM, -⟩ := haA0
  obtain ⟨ld⟩ := exists_linkData hnab hp2 hq hBelow hinv hM𝒞 hM
    (hF3 G hnab hp2 hq K z hz hBelow hconn hind a M hM𝒞 hM)
  obtain ⟨J, t, N, u, hb⟩ := exists_frameBasis hA haA
  obtain ⟨J', t', N', u', hb'⟩ := exists_frameBasis hA' haA'
  have ha2 : a * a = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨cJ', hcJ'⟩ := ld.sec.exists_comp ld.D hb'.linkJ
  obtain ⟨cN', hcN'⟩ := ld.sec.exists_comp ld.D hb'.linkN
  by_cases h1 : cJ = cJ'
  · exact reflTransGen_frameLink_of_comp hinv hp2 ld.sec ld.D ld.h5 hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memJ hb'.clsJ hb'.tB hb'.tqJ hb'.ta
      (by rw [h1]; exact hcJ')
  by_cases h2 : cJ = cN'
  · exact reflTransGen_frameLink_of_comp hinv hp2 ld.sec ld.D ld.h5 hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memN hb'.clsN hb'.uB hb'.tqN hb'.u_ne_a
      (by rw [h2]; exact hcN')
  by_cases hcl : SameClass a t t'
  · have hcl' : ¬ SameClass a t u' := fun h => hb'.not_sameClass ((hcl.symm ha2).trans ha2 h)
    exact frames_link_of_cross ld hp2 hq hinv hcan hMFC hb hb' hb'.memN hb'.clsN hb'.uB hb'.tqN
      hb'.u_ne_a h2 hcJ hcN' hcl'
  · exact frames_link_of_cross ld hp2 hq hinv hcan hMFC hb hb' hb'.memJ hb'.clsJ hb'.tB hb'.tqJ
      hb'.ta h1 hcJ hcJ' hcl

end Main

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem bootTriple_canonClass (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p)
    (hF3 : FuzzyNoF3 p f (canonClass p f)) (hlinkF3 : LinkNoF3 p f (canonClass p f))
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames (canonClass p f) hlay
    (fun _ _ _ K => conjInvariant_canonClass K) (fuzzyFrameBalance_of_hybrid hmodel hF3)
    (fuzzyAxisExact_canonClass p f) (fuzzyVertexConn_canonClass_of_linkNoF3 hlinkF3)
    (fuzzyLinkConn_canonClass hMFC hlinkF3) hcov9 hexotic

end Assembly

end CFSG.ClassicalInvolution.Balance.Bootstrap
