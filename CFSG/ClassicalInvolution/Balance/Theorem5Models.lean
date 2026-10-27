module

public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Balance.LayerGenerationHybrid
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime]

theorem triangleLayers_of_pair (hmodel : LayerGenerationPair) (hF3 : FrameNoF3 p f) :
    TriangleLayers p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact componentLayersAt_of_pair_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) hA hmodel
    (noComponentOverF3_of_frameNoF3 hF3 hnab hp2 hq hz hBelow hconn hA)

theorem triangleLayers_of_hybrid (hmodel : LayerGenerationHybrid p) (hF3 : FrameNoF3 p f) :
    TriangleLayers p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  exact componentLayersAt_of_hybrid_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ
    (localLieSystems_of_citBelowU hΩ hBelow) (memberFamily_of_indepTripleOn hp2 hf hA) hA hmodel
    (noComponentOverF3_of_frameNoF3 hF3 hnab hp2 hq hz hBelow hconn hA)

theorem bootTriple_of_pair_noCover (hmodel : LayerGenerationPair)
    (htri : ConnectedTrianglesExist p f) (hcov9 : p ^ f = 9 → ConnectedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_triangleLayers_noCover (triangleLayers_of_pair hmodel hF3) htri hcov9 hexotic

theorem bootTriple_of_hybrid_noCover (hmodel : LayerGenerationHybrid p)
    (htri : ConnectedTrianglesExist p f) (hcov9 : p ^ f = 9 → ConnectedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) (hF3 : FrameNoF3 p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_triangleLayers_noCover (triangleLayers_of_hybrid hmodel hF3) htri hcov9 hexotic

end CFSG.ClassicalInvolution.Balance.Theorem5
