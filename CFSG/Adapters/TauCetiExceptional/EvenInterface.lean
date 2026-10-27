module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

@[expose] def UntwistedBridgeEven (τ : Tag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card →
      Nonempty (AdjointQuotient τ K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩)

@[expose] def TwistedBridgeEven (t : TwistTag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card ^ t.order →
      ∀ σ : K →+* K, (∀ x, σ x = x ^ q.card) →
        Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
          ValidLieTypeIndex.Group ⟨c q, hv⟩)

structure ChevalleyBridgesEven : Prop where
  g2 : UntwistedBridgeEven .G2 LieTypeIndex.G2
  f4 : UntwistedBridgeEven .F4 LieTypeIndex.F4
  e6 : UntwistedBridgeEven .E6 LieTypeIndex.E6
  e7 : UntwistedBridgeEven .E7 LieTypeIndex.E7
  e8 : UntwistedBridgeEven .E8 LieTypeIndex.E8
  twistedE6 : TwistedBridgeEven .E6 LieTypeIndex.twistedE6
  trialityD4 : TwistedBridgeEven .D4 LieTypeIndex.trialityD4

end CFSG.TauCetiBridge.Even
