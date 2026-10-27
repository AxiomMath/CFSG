module

public import CFSG.ClassicalInvolution.Balance.Q27FuzzyLinkFrames
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnP1

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers commuteAdj FuzzyEdgeInFrame FuzzyLinkConn FuzzyVertexConn
    FuzzyFrameBalance TriangleConnectedAll TriangleLayers conjInvariant_conjMembers
    fuzzyAxisExact_conjMembers fuzzyMemberConn_conjMembers fuzzyVertexConn_of_adj)

section Canon

variable {p f : ℕ} [Fact p.Prime]

theorem fuzzyEdgeInFrame_canonClass_free :
    FuzzyEdgeInFrame p f (canonClass p f) (tqAdj p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind M hM𝒞 N hN𝒞 zM zN hM hN hE hne
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  obtain ⟨a', u', hM', -, -, hNa'⟩ := hE
  have ha' : a' = zM := hM.eq_of_isCentralInvolution hp2 hf hM'.isCentralInvolution
  have haN : zM ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (ha' ▸ hNa')
  have hua : zN ≠ zM := hne.symm
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM𝒞 hM
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
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb hN𝒞 hN haN
      (j := cJ) hcJ (by rw [← h0J]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases h0N : c₀ = c₁
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_comp_free ld hp2 hq hinv hb.swap hN𝒞 hN haN
      (j := c₁) hc₁ (by rw [← h0N]; exact hc₀)
    exact ⟨B, hB, haB, huB⟩
  by_cases hcl : SameClass zM t zN
  · have hcl' : ¬ SameClass zM u₁ zN := fun h => hb.not_sameClass (hcl.trans ha2 (h.symm ha2))
    obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM𝒞 hM hb.memN
      hb.clsN (hb.tqN hb.aB) hb.u_ne_a hN𝒞 hN haN hua (j₁ := c₁) (j₂ := c₀) (Ne.symm h0N) hc₁
      hc₀ hcl'
    exact ⟨B, hB, haB, huB⟩
  · obtain ⟨B, hB, haB, huB⟩ := exists_frame_of_cross_free ld hp2 hq hinv hcan hM𝒞 hM hb.memJ
      hb.clsJ (hb.tqJ hb.aB) hb.ta hN𝒞 hN haN hua (j₁ := cJ) (j₂ := c₀) (Ne.symm h0J) hcJ hc₀
      hcl
    exact ⟨B, hB, haB, huB⟩

theorem fuzzyVertexConn_canonClass_free : FuzzyVertexConn p f (canonClass p f) :=
  fuzzyVertexConn_canonClass fuzzyEdgeInFrame_canonClass_free

theorem fuzzyLinkConn_canonClass_free (hMFC : ModelFacts.CommutingFundamentalFactsFive p) :
    FuzzyLinkConn p f (canonClass p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' haA haA'
  have hinv := conjInvariant_canonClass (p := p) (f := f) K
  have hcan := canonClass_subset (p := p) (f := f) K
  have haA0 := haA
  obtain ⟨-, M, hM𝒞, hM, -⟩ := haA0
  obtain ⟨ld⟩ := exists_linkDataFree hnab hp2 hq hBelow hinv hM𝒞 hM
  obtain ⟨J, t, N, u, hb⟩ := exists_frameBasis hA haA
  obtain ⟨J', t', N', u', hb'⟩ := exists_frameBasis hA' haA'
  have ha2 : a * a = 1 := hb.sq hb.aB
  obtain ⟨cJ, hcJ⟩ := ld.sec.exists_comp ld.D hb.linkJ
  obtain ⟨cJ', hcJ'⟩ := ld.sec.exists_comp ld.D hb'.linkJ
  obtain ⟨cN', hcN'⟩ := ld.sec.exists_comp ld.D hb'.linkN
  by_cases h1 : cJ = cJ'
  · exact reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memJ hb'.clsJ hb'.tB hb'.tqJ hb'.ta
      (by rw [h1]; exact hcJ')
  by_cases h2 : cJ = cN'
  · exact reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb hA' haA' cJ hb.memJ
      hb.clsJ hb.tB hb.tqJ hcJ hb'.memN hb'.clsN hb'.uB hb'.tqN hb'.u_ne_a
      (by rw [h2]; exact hcN')
  by_cases hcl : SameClass a t t'
  · have hcl' : ¬ SameClass a t u' := fun h => hb'.not_sameClass ((hcl.symm ha2).trans ha2 h)
    exact frames_link_of_cross_free ld hp2 hq hinv hcan hMFC hb hb' hb'.memN hb'.clsN hb'.uB hb'.tqN
      hb'.u_ne_a h2 hcJ hcN' hcl'
  · exact frames_link_of_cross_free ld hp2 hq hinv hcan hMFC hb hb' hb'.memJ hb'.clsJ hb'.tB hb'.tqJ
      hb'.ta h1 hcJ hcJ' hcl

theorem bootTriple_canonClass_free (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames (canonClass p f) hlay
    (fun _ _ _ K => conjInvariant_canonClass K) (fuzzyFrameBalance_of_hybrid_free hmodel)
    (fuzzyAxisExact_canonClass p f) fuzzyVertexConn_canonClass_free
    (fuzzyLinkConn_canonClass_free hMFC) hcov9 hexotic

end Canon

section Conj

variable {p f : ℕ} [Fact p.Prime]

theorem fuzzyEdgeInFrame_conjMembers_free : FuzzyEdgeInFrame p f conjMembers commuteAdj := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind M hM N hN zM zN hMc hNc hE hne
  have hK : conjMembers K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  have hadj : tqAdj p f M N := by
    refine ⟨zM, zN, hMc, hNc, ?_, ?_⟩
    · exact mem_trivialOnQuot_iff_actsTrivOnQuot.mp
        (Theorem5.mem_trivialOnQuot_of_centralizes fun x hx => (hE x hx zN hNc.mem).symm)
    · exact mem_trivialOnQuot_iff_actsTrivOnQuot.mp
        (Theorem5.mem_trivialOnQuot_of_centralizes fun y hy => hE zM hMc.mem y hy)
  beta_reduce at hM hN ⊢
  rw [hK] at hM hN ⊢
  exact fuzzyEdgeInFrame_canonClass_free G hnab hp2 hq K z hz hBelow hconn hind M hM N hN zM zN
    hMc hNc hadj hne

theorem fuzzyLinkConn_conjMembers_free (hMFC : ModelFacts.CommutingFundamentalFactsFive p) :
    FuzzyLinkConn p f conjMembers := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' haA haA'
  have hK : conjMembers K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  beta_reduce at hA hA' haA haA' ⊢
  rw [hK] at hA hA' haA haA' ⊢
  exact fuzzyLinkConn_canonClass_free hMFC G hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA'
    haA haA'

theorem bootTriple_conjMembers_free (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames conjMembers hlay
    (fun _ _ _ K => conjInvariant_conjMembers K) (fuzzyFrameBalance_of_hybrid_free hmodel)
    fuzzyAxisExact_conjMembers
    (fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers fuzzyEdgeInFrame_conjMembers_free)
    (fuzzyLinkConn_conjMembers_free hMFC) hcov9 hexotic

end Conj

section Connected

variable {p f : ℕ} [Fact p.Prime]

theorem fuzzyFramesConnected_conjMembers_free (hMFC : ModelFacts.CommutingFundamentalFactsFive p) :
    FuzzyFramesConnected p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hmap : ∀ A ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K) :=
    fun A hA g => Theorem5.FuzzyFrameOn.map (conjInvariant_conjMembers K) hA g
  have hvert := fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers
    (fuzzyEdgeInFrame_conjMembers_free (p := p) (f := f))
  have hlink := fuzzyLinkConn_conjMembers_free (f := f) hMFC
  exact Theorem5.shareFour_connected_of_vertexGraph_modOdd
    (𝒯 := Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K)) hmap
    (fun A hA => by
      obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) (fun A _ z hz => hz.1)
    (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' =>
      hvert G hnab hp2 hq K z hz hBelow hconn hind a a'
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha; exact ⟨J, hJ, hJa⟩)
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha'; exact ⟨J, hJ, hJa⟩))
    (fun a A hA A' hA' ha ha' =>
      hlink G hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' ha ha')

theorem triangleConnectedAll_conjMembers_free (hlay : TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    TriangleConnectedAll p f :=
  triangleConnectedAll_of_bootTriple (bootTriple_conjMembers_free hlay hmodel hMFC hcov9 hexotic)
    (fuzzyFramesConnected_conjMembers_free hMFC)

theorem productOfTwoP1_of_indepTriple_free (hlay : TriangleLayers p f)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ M ∈ CoreAssembly.conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M →
          z ≠ w → LocalOddCentral (CoreAssembly.conjClass K) {z * w} := by
  intro G _ _ _ hnab K z S hind M hM w hw hKM hzw
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; have := S.five; simp at this)
  have hlay' : ∀ A' : Subgroup G, IndepTripleOn p f (CoreAssembly.conjClass K) A' →
      ∀ a ∈ A', a ≠ 1 → ComponentLayersAt (CoreAssembly.conjClass K) A' a := fun A' hA' =>
    hlay G hnab S.odd S.five K z S.cls S.below S.conn A' hA'
  have hadj := fuzzyEdgeInFrame_conjMembers_free G hnab S.odd S.five K z S.cls S.below S.conn
    hind K (CoreAssembly.mem_conjClass_self K) M hM z w S.cls hw hKM hzw
  have hbal := fuzzyFramesBalanced_of_exact hnab S.odd hf S.five S.inClass S.ih S.exact hlay'
  have hcon := fuzzyFramesConnected_conjMembers_free (f := f) hMFC G hnab S.odd S.five K z S.cls
    S.below S.conn hind
  exact Theorem5.localOddCentral_mul_of_frameAdj hnab S.odd S.five S.inClass S.ih S.exact hlay'
    hbal hcon hzw hadj

end Connected

end CFSG.ClassicalInvolution.Balance.Q27
