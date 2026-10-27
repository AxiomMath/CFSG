module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootNoTwins
public import CFSG.ClassicalInvolution.Asc77.AscFusionB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem hypOmegaModAll_of_fusionCore (h : AscFusion.FusionCoreStmt p f) :
    HypOmegaModAll p f :=
  AscHypOmega.hypOmegaAllStmt_of_fusion (AscFusion.classicalFusionStmt_of_fusionCore h)

structure BootNoTripleResiduals (p f : ℕ) [Fact p.Prime] : Prop where
  shape : BootShapeCover p f
  genChain : ChainFrameGenT p f
  hyp51t : ChainFrameHyp51t p f
  hyp51zt : ChainFrameHyp51zt p f
  aEmptyTwin : AEmptyTwinExact p f
  genTwin : TwinFrameGenT p f
  twinSmallInner : TwinSmallInner p
  twinSmallOuter : TwinSmallOuter p
  g2d4VertexExcl : G2D4VertexExcl p f

theorem BootNoTripleInputs.of_fusionCore (hfus : AscFusion.FusionCoreStmt p f)
    (h : BootNoTripleResiduals p f) : BootNoTripleInputs p f :=
  have hΩ : HypOmegaModAll p f := hypOmegaModAll_of_fusionCore hfus
  { shape := h.shape
    hypOmega := hΩ
    aEmptyChain := aEmptyChain_of_hypOmega hΩ
    noTwinsChain := noTwinsChain_of_hypOmega hΩ
    genChain := h.genChain
    hyp51t := h.hyp51t
    hyp51zt := h.hyp51zt
    aEmptyTwin := h.aEmptyTwin
    twinSmallInner := h.twinSmallInner
    twinSmallOuter := h.twinSmallOuter
    g2d4VertexExcl := h.g2d4VertexExcl
    genTwin := h.genTwin }

theorem bootNoTripleD_of_fusionCore (hfus : AscFusion.FusionCoreStmt p f)
    (h : BootNoTripleResiduals p f) : BootNoTripleD p f :=
  (BootNoTripleInputs.of_fusionCore hfus h).bootNoTripleD

end CFSG.ClassicalInvolution.Asc77
