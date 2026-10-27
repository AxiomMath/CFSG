module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj
public import CFSG.ClassicalInvolution.Balance.Theorem5FuzzyExact

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers fuzzyFrames fuzzyVertices ShareFourIn TriangleConnected
    TriangleConnectedAll TriangleLayers conjInvariant_conjMembers fuzzyMemberConn_conjMembers
    fuzzyVertexConn_of_adj)

section Connected

variable {p f : ℕ} [Fact p.Prime]

@[expose] def FuzzyFramesConnected (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ A ∈ fuzzyFrames p f (CoreAssembly.conjClass K),
          ∀ A' ∈ fuzzyFrames p f (CoreAssembly.conjClass K),
            Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f (CoreAssembly.conjClass K))) A A'

theorem fuzzyFramesConnected_conjMembers (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hF3 : LinkNoF3 p f conjMembers) : FuzzyFramesConnected p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hmap : ∀ A ∈ fuzzyFrames p f (CoreAssembly.conjClass K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ fuzzyFrames p f (CoreAssembly.conjClass K) :=
    fun A hA g => Theorem5.FuzzyFrameOn.map (conjInvariant_conjMembers K) hA g
  have hvert := fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers
    (fuzzyEdgeInFrame_conjMembers hF3)
  have hlink := fuzzyLinkConn_conjMembers hMFC hF3
  exact Theorem5.shareFour_connected_of_vertexGraph_modOdd
    (𝒯 := fuzzyFrames p f (CoreAssembly.conjClass K)) hmap
    (fun A hA => by
      obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (fuzzyVertices p f (CoreAssembly.conjClass K)) (fun A _ z hz => hz.1)
    (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' =>
      hvert G hnab hp2 hq K z hz hBelow hconn hind a a'
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha; exact ⟨J, hJ, hJa⟩)
        (by obtain ⟨-, J, hJ, hJa, -⟩ := ha'; exact ⟨J, hJ, hJa⟩))
    (fun a A hA A' hA' ha ha' =>
      hlink G hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' ha ha')

end Connected

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem indepTriple_of_indepTripleOn {Ω : Set (Subgroup G)} {A : Subgroup G}
    (h : IndepTripleOn p f Ω A) : CoreAssembly.IndepTriple p f Ω := by
  obtain ⟨K', z', hK', hcomm, hAdef, hel, hcard⟩ := h
  subst hAdef
  exact ⟨K', z', hK', hcomm, hel, hcard⟩

theorem triangleConnected_of_fuzzyFramesConnected [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hcon : ∀ A ∈ fuzzyFrames p f Ω, ∀ A' ∈ fuzzyFrames p f Ω,
      Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f Ω)) A A') :
    TriangleConnected p f Ω := by
  intro A hA A' hA'
  have key : ∀ B : Subgroup G, Relation.ReflTransGen (ShareFourIn (fuzzyFrames p f Ω)) A B →
      Relation.ReflTransGen (fun X Y => X ∈ Theorem5.triangleFrames p f Ω ∧
        Y ∈ Theorem5.triangleFrames p f Ω ∧ ShareFour X Y) A B := by
    intro B h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨hX, hY, hXY⟩ := hbc
      exact ih.tail ⟨Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hX,
        Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hY, hXY⟩
  exact key A' (hcon A (Theorem5.fuzzyFrameOn_of_indepTripleOn hA) A'
    (Theorem5.fuzzyFrameOn_of_indepTripleOn hA'))

theorem fuzzyFramesBalanced_of_exact [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hex : ExactMembers Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a) :
    ∀ A ∈ fuzzyFrames p f Ω, RankThreeBalance A := fun A hA => by
  have hT := Theorem5.FuzzyFrameOn.indepTripleOn_of_exact hnab hp2 hq hΩ hIH hex hA
  exact Theorem5.rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hT (hlay A hT)

theorem triangleConnectedAll_of_bootTriple (hBT : CoreAssembly.BootTriple p f)
    (hcon : FuzzyFramesConnected p f) : TriangleConnectedAll p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA A' hA'
  have hind : CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) :=
    indepTriple_of_indepTripleOn hA
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hex := (hBT G hnab hp2 hq K z hz hBelow hconn hind).1
  exact triangleConnected_of_fuzzyFramesConnected hnab hp2 hq hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) hex (hcon G hnab hp2 hq K z hz hBelow hconn hind)
    A hA A' hA'

theorem triangleConnectedAll_conjMembers (hlay : TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hF3 : FuzzyNoF3 p f conjMembers)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    TriangleConnectedAll p f :=
  triangleConnectedAll_of_bootTriple
    (bootTriple_conjMembers hlay hmodel hF3 hlinkF3 hMFC hcov9 hexotic)
    (fuzzyFramesConnected_conjMembers hMFC hlinkF3)

end Triangle

section P1

variable {p f : ℕ} [Fact p.Prime]

theorem productOfTwoP1_of_indepTriple (hlay : TriangleLayers p f)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p) :
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
  have hadj := fuzzyEdgeInFrame_conjMembers hlinkF3 G hnab S.odd S.five K z S.cls S.below S.conn
    hind K (CoreAssembly.mem_conjClass_self K) M hM z w S.cls hw hKM hzw
  have hbal := fuzzyFramesBalanced_of_exact hnab S.odd hf S.five S.inClass S.ih S.exact hlay'
  have hcon := fuzzyFramesConnected_conjMembers hMFC hlinkF3 G hnab S.odd S.five K z S.cls
    S.below S.conn hind
  exact Theorem5.localOddCentral_mul_of_frameAdj hnab S.odd S.five S.inClass S.ih S.exact hlay'
    hbal hcon hzw hadj

end P1

end CFSG.ClassicalInvolution.Balance.Bootstrap
