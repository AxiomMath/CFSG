module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpERed
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def OuterNotSylowCentral (S : Type) [Group S] [Finite S] : Prop :=
  ∀ σ : MulAut S, σ * σ = 1 → ∀ T : Sylow 2 S, (∀ t ∈ (T : Subgroup S), σ t = t) →
    σ ∈ (MulAut.conj : S →* MulAut S).range

@[expose] def FixedA8KernelTrivial (S : Type) [Group S] [Finite S] : Prop :=
  ∀ Q : Subgroup (MulAut S), (∀ q ∈ Q, q * q = 1) → Nat.card Q ≤ 2 →
    ∀ T : Subgroup S, T ≤ EvenPump.autFixed Q →
      IsPComponent 2 (T.subgroupOf (EvenPump.autFixed Q)) →
      Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 20160 → coreActionKernel T = ⊥

@[expose] def GS82R18Input : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (Blueprint.LieModel S .PSL 4 2 2 ∨ Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HS)) →
    OuterNotSylowCentral S ∧ FixedA8KernelTrivial S

end CFSG.ComponentClassification.GSThmB.A10T
