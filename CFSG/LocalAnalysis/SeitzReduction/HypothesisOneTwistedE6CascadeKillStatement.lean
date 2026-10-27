module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKillBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def TwistedE6KillFixed
    (K : Type) [Field K] (σ : K →+* K) : Prop :=
  ∀ J : Set (Fin TwistTag.E6.tag.rank), (∀ j ∈ J, TwistTag.E6.perm j ∈ J) →
    ∀ i ∈ J, TwistTag.E6.perm i = i → ∀ c : K, c ≠ 0 → σ c = c →
      ∀ u ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1}),
        u ∈ twistedFixedGroup TwistTag.E6 K σ →
        (pinnedX TwistTag.E6.tag K (Pi.single i 1) c * u) ^ 2 = 1 →
        ∃ p ∈ rootSpan TwistTag.E6.tag K
            (parabolicPosRoots TwistTag.E6.tag J \ {Pi.single i 1}),
          p ∈ twistedFixedGroup TwistTag.E6 K σ ∧
          ∃ u'' ∈ rootSpan TwistTag.E6.tag K (classKillPerp TwistTag.E6.tag J i),
            u'' ∈ twistedFixedGroup TwistTag.E6 K σ ∧
            p * (pinnedX TwistTag.E6.tag K (Pi.single i 1) c * u) * p⁻¹ =
              pinnedX TwistTag.E6.tag K (Pi.single i 1) c * u''

@[expose] def TwistedE6KillPair
    (K : Type) [Field K] (σ : K →+* K) : Prop :=
  ∀ J : Set (Fin TwistTag.E6.tag.rank), (∀ j ∈ J, TwistTag.E6.perm j ∈ J) →
    ∀ i ∈ J, TwistTag.E6.perm i ≠ i → ∀ c : K, c ≠ 0 →
      ∀ u ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
          {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}),
        u ∈ twistedFixedGroup TwistTag.E6 K σ →
        (twistedE6PairX σ (Pi.single i 1) c * u) ^ 2 = 1 →
        ∃ p ∈ rootSpan TwistTag.E6.tag K (parabolicPosRoots TwistTag.E6.tag J \
            {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}),
          p ∈ twistedFixedGroup TwistTag.E6 K σ ∧
          ∃ u'' ∈ rootSpan TwistTag.E6.tag K (classKillPerp TwistTag.E6.tag J i ∩
              classKillPerp TwistTag.E6.tag J (TwistTag.E6.perm i)),
            u'' ∈ twistedFixedGroup TwistTag.E6 K σ ∧
            p * (twistedE6PairX σ (Pi.single i 1) c * u) * p⁻¹ =
              twistedE6PairX σ (Pi.single i 1) c * u''

@[expose] def TwistedE6Kill
    (K : Type) [Field K] (σ : K →+* K) : Prop :=
  TwistedE6KillFixed K σ ∧ TwistedE6KillPair K σ

end CFSG.SeitzReduction
