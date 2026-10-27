module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XRes
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (fieldActor)

@[expose] def K148InnerCentFact : Prop :=
  ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentAt f

@[expose] def K148G2SimpleFact : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (f : ℕ), 2 ≤ f → Nat.card K = (2 ^ f) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ f) →
    IsSimpleGroup ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ))

@[expose] def K148TwoG2Fact : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ 1) ^ 3 → (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ (H : Type) [Group H] (e : H ≃* ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)))
      (S : Subgroup H), S.IsSubnormal → ∀ (Q : Type) [Group Q] (φ : ↥S →* Q), Function.Surjective φ →
      CFSG.Open.IsQuasisimple Q →
      catalogIs Q (onLie fun | .twistedA 2 q => q.card = 3 | _ => False)

end CFSG.LocalAnalysis.GLTheoremA

end
