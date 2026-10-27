module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmTransport
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

@[expose] def KD264OmPlusCore : Prop :=
  ∀ (n : ℕ), 5 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    OmCoreShape (StatedProj (StatedOmega (StatedQuadPlus n K)))

@[expose] def KD264OmMinusCore : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      OmCoreShape (StatedProj (StatedOmega (StatedQuadMinus n K b c)))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
