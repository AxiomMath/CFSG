module

public import CFSG.ClassicalInvolution.Asc77.AscT8U1
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices LinkMove)
open CFSG.ClassicalInvolution.Balance.Q27
  (exists_linkDataFree frames_link_of_cross_free reflTransGen_frameLink_of_comp_free
    rankThreeBalance_of_fuzzyFrameOn_hybrid_free)

namespace T8U

section Link

variable {p f : ℕ} [Fact p.Prime]


theorem fuzzyLinkConn_canonClass (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (K : Subgroup G) (hBelow : CITBelowU p f (Nat.card G))
    (a : G) {A A' : Subgroup G} (hA : A ∈ fuzzyFrames p f (canonClass p f K))
    (hA' : A' ∈ fuzzyFrames p f (canonClass p f K))
    (haA : a ∈ fuzzyVertices p f (canonClass p f K) A)
    (haA' : a ∈ fuzzyVertices p f (canonClass p f K) A') :
    Relation.ReflTransGen (LinkMove (fuzzyFrames p f (canonClass p f K))
      (fuzzyVertices p f (canonClass p f K)) a) A A' := by
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

theorem alphaOf_eq_of_fuzzyFrames {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G)) (a : G)
    {A A' : Subgroup G} (hA : FuzzyFrameOn p f (CoreAssembly.conjClass K) A)
    (hA' : FuzzyFrameOn p f (CoreAssembly.conjClass K) A')
    (haA : a ∈ fuzzyVertices p f (CoreAssembly.conjClass K) A)
    (haA' : a ∈ fuzzyVertices p f (CoreAssembly.conjClass K) A') {F F' : Subgroup G}
    (hF : F ≤ A) (hF4 : Nat.card F = 4) (hF' : F' ≤ A') (hF'4 : Nat.card F' = 4) :
    alphaOf F = alphaOf F' := by
  have hc : canonClass p f K = CoreAssembly.conjClass K := canonClass_eq_conjClass hz
  rw [← hc] at hA hA' haA haA'
  have hMFC := ModelFacts.commutingFundamentalFactsFive_all (p := p) hp2
  have hchain := fuzzyLinkConn_canonClass hMFC hnab hp2 hq K hBelow a hA hA' haA haA'
  refine alphaOf_eq_of_reflTransGen_linkMove (𝒯 := fuzzyFrames p f (canonClass p f K))
    (cl := fuzzyVertices p f (canonClass p f K)) (a := a) ?_ ?_ hA hchain hF hF4 hF' hF'4
  · intro B hB
    exact rankThreeBalance_of_fuzzyFrameOn_hybrid_free hnab hp2 hq hBelow hB
      (layerGenerationHybrid p)
  · intro B _ w hw
    exact hw.1

end Link

end T8U

end CFSG.ClassicalInvolution.Asc77
