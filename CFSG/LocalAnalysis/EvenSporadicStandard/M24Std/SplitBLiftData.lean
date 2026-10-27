module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBBasis

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def liftSw : List ℤ :=
  [1, 2, 1, -2, 1, 2, 1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1,
   2, -1, -2, -1, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2,
   1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1,
   2, 1, -2, 1, -2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2,
   1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2]

@[expose] def liftTw : List ℤ :=
  [2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -2, -1, 2, -1, 2,
   -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, 1, -2, 1, 2, 1, -2, 1,
   -2, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2,
   -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1, -2, 1, 2, 1, -2,
   1, -2, 1, 2, 1, 2, 1, -2, 1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1,
   -2]

@[expose] def liftS : S24 := m24Cj liftSw

@[expose] def liftT : S24 := m24Cj liftTw

@[expose] def LiftBData : Prop :=
  NormB0 liftS ∧ NormB0 liftT ∧ liftS * liftS = 1 ∧ liftT * liftT = 1 ∧
    (liftS * liftT) * (liftS * liftT) = 1 ∧
    (∀ i, liftS * fB i * liftS⁻¹ = ebasis4 fB (M23Std.liftA1 i)) ∧
    ∀ i, liftT * fB i * liftT⁻¹ = ebasis4 fB (M23Std.liftA2 i)

instance : Decidable LiftBData := by unfold LiftBData; infer_instance

end CFSG.EvenSporadicStandard.M24Std.SplitB
