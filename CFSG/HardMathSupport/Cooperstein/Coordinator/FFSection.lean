module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding

@[expose] def NoIrrFFOffender (Y : Type) [Group Y] : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L →
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn L →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
        Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def IsSQTKSporadic (n : TauCeti.SporadicName) : Prop :=
  n = .M11 ∨ n = .M12 ∨ n = .M22 ∨ n = .M23 ∨ n = .M24 ∨ n = .J1 ∨ n = .J2 ∨ n = .J4 ∨
    n = .HS ∨ n = .He ∨ n = .Ru

@[expose] def IsSQTKOddLieIndex : TauCeti.LieTypeIndex → Prop
  | .A 1 q => (q.exponent = 1 ∧ 11 ≤ q.p) ∨ (q.exponent = 2 ∧ 5 ≤ q.p)
  | .A 2 q => q.exponent = 1 ∧ q.p ≠ 2
  | .twistedA 2 q => q.exponent = 1 ∧ 5 ≤ q.p
  | _ => False

@[expose] def IsSQTKExceptionalTwoIndex : TauCeti.LieTypeIndex → Prop
  | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | _ => False

end CFSG.HardMathSupport.Cooperstein.Coordinator
