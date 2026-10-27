module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

section Cover

variable (p f : ℕ) [Fact p.Prime]

@[expose] def BootShapeCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) →
      BootData p f (CoreAssembly.conjClass K) → ¬ IndepTriple p f (CoreAssembly.conjClass K) →
        ChainShape p f (CoreAssembly.conjClass K) z ∨ TwinExactShape p f K z

end Cover

section Assembly

variable {p f : ℕ} [Fact p.Prime]

theorem bootNoTripleD_of_frames (hshape : BootShapeCover p f)
    (hch : FrameExistsOnE p f (ChainShapePred (p := p) (f := f)))
    (htw : FrameExistsOnE p f (TwinExactShapePred (p := p) (f := f))) : BootNoTripleD p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hdata hT
  obtain ⟨L₀, z₀, A, S, a, hfr, hA⟩ : ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G)
      (S : Set (Subgroup G)) (a : G),
      FuzzyFrameDataStarE p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧ Hyp51 A := by
    rcases hshape G hnab hp2 hq K z hz hBelow hconn hdata hT with hs | hs
    · exact hch G hnab hp2 hq K z hz hBelow hconn hs
    · exact htw G hnab hp2 hq K z hz hBelow hconn hs
  have hΩ := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_fuzzyFrameStarE hnab hp2 hq hΩ
    (exists_single_class K) hIH hconn hfr (lemma52 G A hA)
  exact ⟨hex, hP1 K (mem_conjClass_self K) z hz⟩

theorem bootNoTripleD_of_inputs (hshape : BootShapeCover p f) (hΩ : HypOmegaModAll p f)
    (hAc : AEmptyChain p f) (hTc : NoTwinsChain p f) (hGenC : ChainFrameGenT p f)
    (h51t : ChainFrameHyp51t p f) (h51zt : ChainFrameHyp51zt p f) (hAt : AEmptyTwinExact p f)
    (hH : TwinFrameHyp51 p f) (hGenT : TwinFrameGenT p f) : BootNoTripleD p f :=
  bootNoTripleD_of_frames hshape
    (chainFrame_exists_on_of_lemma52' hΩ hAc hTc hGenC h51t h51zt lemma52)
    (twinFrame_exists_on hΩ hAt G2D4Models.ih8G2D4_unconditional hH hGenT)

structure BootNoTripleInputs (p f : ℕ) [Fact p.Prime] : Prop where
  shape : BootShapeCover p f
  hypOmega : HypOmegaModAll p f
  aEmptyChain : AEmptyChain p f
  noTwinsChain : NoTwinsChain p f
  genChain : ChainFrameGenT p f
  hyp51t : ChainFrameHyp51t p f
  hyp51zt : ChainFrameHyp51zt p f
  aEmptyTwin : AEmptyTwinExact p f
  twinSmallInner : TwinSmallInner p
  twinSmallOuter : TwinSmallOuter p
  g2d4VertexExcl : G2D4VertexExcl p f
  genTwin : TwinFrameGenT p f

theorem BootNoTripleInputs.bootNoTripleD (h : BootNoTripleInputs p f) : BootNoTripleD p f :=
  bootNoTripleD_of_inputs h.shape h.hypOmega h.aEmptyChain h.noTwinsChain h.genChain h.hyp51t
    h.hyp51zt h.aEmptyTwin (twinFrameHyp51_of h.twinSmallInner h.twinSmallOuter h.g2d4VertexExcl)
    h.genTwin

end Assembly

end CFSG.ClassicalInvolution.Asc77
