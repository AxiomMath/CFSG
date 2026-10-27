module

public import CFSG.ClassicalInvolution.Balance.QNineFuzzyQuasi
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnP1

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Family

theorem exactMembers_and_localOddCentral_of_balancedFamily_exotic [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hconn : OmegaConnected Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A')
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hA : A ∈ 𝒯) (hexotic : ExoticLeviBlock p f) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ w : G, IsClassicalMember p f L w → LocalOddCentral Ω {w} := by
  by_cases h9 : p ^ f = 9
  · have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq
      · exact h
    have hO := componentClassificationOddCore_eq_bot_of_simple hnab
    have hα := alphaCore_eq_bot_of_connected_frames hO hinv hbal hcon
    have hΔ := deltaCore_eq_bot_of_connected_frames hO hinv hbal hcon
    obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal A hA)
    have hK0A : K 0 ≤ Subgroup.centralizer (A : Set G) := by
      rw [hAdef]
      exact triple_centralizes hK hcomm 0
    have hq0 : CFSG.Open.IsQuasisimple (K 0) :=
      isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩ hIH (hK 0).1 (hK 0).2
        (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hel hF₀.1)
        (hK0A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ A hA F₀ hF₀)
    have hqs := isQuasisimple_of_mem_of_single_class hsingle (hK 0).1 hq0
    have hP1 : LocalOddCentral Ω {z 0} :=
      localOddCentral_of_indepTriple_pair_of_isQuasisimple hnab hp2 hq hΩ hIH hqs hlay hK hcomm
        hAdef hel hcard hF₀ (hα A hA F₀ hF₀) (i := 0) (j := 1) (by decide) (x := z 0)
        (Subgroup.subset_closure (by simp)) (hK 0).2.ne_one
    have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hK 0).1 (hK 0).2 hP1
    exact ⟨exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH hconn hP1all hexotic,
      hP1all⟩
  · exact exactMembers_and_localOddCentral_of_balancedFamily hnab hp2 hq h9 hΩ hsingle hIH hlay
      hbal hinv hcon hK hcomm hAdef hel hcard hA

end Family

section BootTriple

theorem bootTriple_of_fuzzyFrames_exotic (𝒞 : MemberClass) (hlay : TriangleLayers p f)
    (hinv : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), ConjInvariant (𝒞 K))
    (hbal : FuzzyFrameBalance p f 𝒞) (hexact : FuzzyAxisExact p f 𝒞)
    (hvert : FuzzyVertexConn p f 𝒞) (hlink : FuzzyLinkConn p f 𝒞)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hind' := hind
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
    ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
  have hA : Subgroup.closure (Set.range z') ∈ fuzzyFrames p f (𝒞 K) :=
    hexact G hnab hp2 hq K z hz hBelow hconn _ hAex
  have hmap : ∀ A ∈ fuzzyFrames p f (𝒞 K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ fuzzyFrames p f (𝒞 K) := fun A hA g =>
    FuzzyFrameOn.map (hinv G K) hA g
  have hcon := shareFour_connected_of_vertexGraph_modOdd (𝒯 := fuzzyFrames p f (𝒞 K)) hmap
    (fun A hA => by
      obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (fuzzyVertices p f (𝒞 K)) (fun A _ z hz => hz.1) (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' =>
      hvert G hnab hp2 hq K z hz hBelow hconn hind' a a'
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha; exact ⟨J, hJ, hJa⟩)
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha'; exact ⟨J, hJ, hJa⟩))
    (fun a A hA A' hA' ha ha' =>
      hlink G hnab hp2 hq K z hz hBelow hconn hind' a A hA A' hA' ha ha')
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_balancedFamily_exotic hnab hp2 hq hΩ
    (CoreAssembly.exists_single_class K) hIH (omegaConnected_of_deltaConnected hconn)
    (fun A' hA' => hlay G hnab hp2 hq K z hz hBelow hconn A' hA')
    (fun A hA => hbal G hnab hp2 hq K z hz hBelow hconn hind' A hA) hmap hcon hK' hcomm rfl hel
    hcard hA hexotic
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end BootTriple

end CFSG.ClassicalInvolution.Balance.Theorem5

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers conjInvariant_conjMembers fuzzyAxisExact_conjMembers
    fuzzyMemberConn_conjMembers fuzzyVertexConn_of_adj TriangleConnectedAll)

section Conj

variable {p f : ℕ} [Fact p.Prime]

theorem bootTriple_conjMembers_exotic (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hF3 : FuzzyNoF3 p f conjMembers)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames_exotic conjMembers hlay
    (fun _ _ _ K => conjInvariant_conjMembers K) (fuzzyFrameBalance_conjMembers hmodel hF3)
    fuzzyAxisExact_conjMembers
    (fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers (fuzzyEdgeInFrame_conjMembers hlinkF3))
    (fuzzyLinkConn_conjMembers hMFC hlinkF3) hexotic

theorem connectedFramesExist_of_bootTriple (hBT : CoreAssembly.BootTriple p f)
    (hcon : FuzzyFramesConnected p f) : Theorem5.ConnectedFramesExist p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hex := (hBT G hnab hp2 hq K z hz hBelow hconn hind).1
  have hqs : ∀ J ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple J := fun J hJ =>
    isQuasisimple_of_mem_exactMembers hq hΩ hex hJ
  have hind' := hind
  obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
  have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
    ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
  have hz'A : ∀ m, z' m ∈ Subgroup.closure (Set.range z') := fun m =>
    Subgroup.subset_closure ⟨m, rfl⟩
  have htri : Theorem5.TriangleConnected p f (CoreAssembly.conjClass K) :=
    triangleConnected_of_fuzzyFramesConnected hnab hp2 hq hΩ hIH hex
      (hcon G hnab hp2 hq K z hz hBelow hconn hind')
  refine ⟨Theorem5.triangleFrames p f (CoreAssembly.conjClass K), fun _ h => h,
    fun _ hA g => Theorem5.indepTripleOn_map hΩ.conjInvariant hA g, htri,
    Subgroup.closure (Set.range z'), hAex, K' 0,
    ⟨(hK' 0).1, triple_centralizes hK' hcomm 0, z' 0, hz'A 0, (hK' 0).2⟩, z' 0, hz'A 0, (hK' 0).2,
    ?_⟩
  exact Theorem5.triangleFramesMeetAt_of_indepTriple_pair_of_isQuasisimple hnab hp2 hf hΩ hIH hqs
    hK' hcomm rfl hel hcard (i := 0) (j := 1) (by decide) (x := z' 0)
    (Subgroup.subset_closure (by simp)) (hK' 0).2.ne_one

theorem triangleConnectedAll_conjMembers_exotic (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hF3 : FuzzyNoF3 p f conjMembers)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hexotic : ExoticLeviBlock p f) : TriangleConnectedAll p f :=
  triangleConnectedAll_of_bootTriple
    (bootTriple_conjMembers_exotic hlay hmodel hF3 hlinkF3 hMFC hexotic)
    (fuzzyFramesConnected_conjMembers hMFC hlinkF3)

theorem connectedFramesExist_conjMembers_exotic (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hF3 : FuzzyNoF3 p f conjMembers)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hexotic : ExoticLeviBlock p f) : Theorem5.ConnectedFramesExist p f :=
  connectedFramesExist_of_bootTriple
    (bootTriple_conjMembers_exotic hlay hmodel hF3 hlinkF3 hMFC hexotic)
    (fuzzyFramesConnected_conjMembers hMFC hlinkF3)

end Conj

end CFSG.ClassicalInvolution.Balance.Bootstrap
