module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Chevalley.ToralSign (signMaskChar)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


@[expose] def BurgoyneE2TwistedE6T1Input : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 2 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, t ^ 2 = 1 →
        ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p],
          (∃ g₁ ∈ adjointGroup TwistTag.E6.tag L,
            frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₁ = g₁ ∧
            g₁ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₁⁻¹ =
              rootDiagUnit TwistTag.E6.tag
                (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) →
          BurgCoreFor (MulAut.conj t) ∨ BurgTorusFor (MulAut.conj t)

end CFSG.ComponentClassification.Burgoyne.E2
