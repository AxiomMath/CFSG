module

public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesFinal
public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLLtProof
public import CFSG.LieType.SeitzGeneration.SeitzFrontier
public import CFSG.LieType.SeitzGeneration.OuterOrth
public import CFSG.LieType.SeitzGeneration.OuterDFour
public import CFSG.LieType.SeitzGeneration.RootPairSpOdd
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.LieType.SeitzGeneration

theorem kFactSeitzRankTwoInnerEx_of_planes (hParEx : ExcParabolicPlane)
    (hAni : SeitzExcAnisotropic) : KFactSeitzRankTwoInnerEx := by
  refine kFactSeitzRankTwoInnerEx_of_for (innerExFor_classical_of_heisCore unitaryHeisCore) ?_
  have hXI := seitzExcLow_of seitzExcParabolic hAni
  intro d hx p hp hp2 hpd hex ⟨E, hE, hc, hi⟩
  by_cases hr : RankLE2 p (Cat d)
  · exact ⟨E, hE, hc, hi, hXI d p hp hp2 hpd hex E hE hc ⟨hi, hr, hx⟩⟩
  · obtain ⟨E₁, hE₁, hc₁, hi₁, hN₁⟩ := hParEx d p hp hp2 hpd hex hx hr
    exact ⟨E₁, hE₁, hc₁, hi₁, seitzExcParabolic d p hp hp2 hpd hex E₁ hE₁ hc₁ ⟨hi₁, hx, hN₁⟩⟩

theorem kFactSeitzRankTwoInnerEx_of_aniso (hAni : SeitzExcAnisotropic) :
    KFactSeitzRankTwoInnerEx :=
  kFactSeitzRankTwoInnerEx_of_planes excParabolicPlane_proved hAni

theorem kFactSeitzRankTwoInnerEx_of_anisoN
    (hAniN : CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus) :
    KFactSeitzRankTwoInnerEx :=
  kFactSeitzRankTwoInnerEx_of_aniso
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.seitzExcAnisotropic_of_cover
      CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.seitzExcAnisotropicG2ThreePlus_proved
      hAniN)

theorem innerEx_lowN_of_pairs_aniso
    (hSpF2 : SubfieldPairSpF2) (hSU2 : SubfieldPairSUOddTwo)
    (hOP : SubfieldPairOmegaPlusChar2) (hOM : SubfieldPairOmegaMinusChar2)
    (hAniN : CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus)
    (hXN : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      ¬ IsClassicalIndex d.1) :
    KFactSeitzRankTwoInnerEx ∧ KFactSeitzRankTwoLowN :=
  innerEx_lowN_of_frontier unitaryHeisCore (unitaryOuterHeisCore_of_finite_cases
      HeisSmall.outerB12AtCard_five HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven) subfieldPairSLLt
      (subfieldPairSpOdd hSpF2) (subfieldPairSUOdd hSU2)
      (seitzOuter_orthogonal_narrow (subfieldPairOmega_of_char2 hOP hOM)) seitzExcParabolic
      excParabolicPlane_proved
      (Seitz.G2Anisotropic.Coordinator.seitzExcAnisotropic_of_cover
          Seitz.G2Anisotropic.ExceptionsTransport.seitzExcAnisotropicG2ThreePlus_proved hAniN)
      (seitzXON_of_nonclassical hXN)

end CFSG.HardMathSupport.Malle.SeitzCube
