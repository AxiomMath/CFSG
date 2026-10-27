module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LinearDegreeNormalizerSolvable
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProduct

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G] [Finite G]

theorem linearSuzukiHullOddCoreTrivial
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G) :
    LinearSuzukiHullOddCoreTrivial G := by
  intro H z h beta hbeta t ht hrank w hwE hw hwz hwt i hi hfix
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hodd, -⟩ :=
    RankOnePair.linear_Suzuki_pair_centralizer_point_kernel_is_root_product h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) hgen beta hbeta ht hrank
      hwE hw hwz hwt hi hfix R Rv T₁
  exact hodd

theorem linearSuzukiPointKernelRootClauses
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G) :
    LinearSuzukiPointKernelRootClauses G := by
  intro H z h beta hbeta t ht hrank w hwE hw hwz hwt i hi hfix
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨Rv⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z (w * z) ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  have key := fun R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H) =>
    RankOnePair.linear_Suzuki_pair_centralizer_point_kernel_is_root_product h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) hgen beta hbeta ht hrank
      hwE hw hwz hwt hi hfix R Rv T₁
  obtain ⟨-, -, -, -, -, -, -, -, hK, -⟩ := key R₀
  refine ⟨hK, fun R => ?_⟩
  obtain ⟨-, -, -, -, hcard, -, -, -, -, -, -, -, hB, hdisj, hcomm, -⟩ := key R
  exact ⟨hcard, hB, hdisj, hcomm⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
