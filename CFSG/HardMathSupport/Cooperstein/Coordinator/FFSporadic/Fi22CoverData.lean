module

public import Certificates.Certificate129041
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint

theorem fi22_coverData :
    ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : NativeSporadic.Fi22,
      Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n :=
  Certificates.certificate129041

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
