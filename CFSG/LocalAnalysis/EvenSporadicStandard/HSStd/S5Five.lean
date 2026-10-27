module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def GoodInvolution {K : Type*} [Group K] (x : K) : Prop :=
  Nonempty (↥(centralizer ({x} : Set K)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))

@[expose] def HaradaFourInspection : Prop :=
  ∀ (K : Type) [Group K] [Finite K], fusionZStar K = ⊥ → HaradaOneList K →
    ∀ a b : K, orderOf a = 2 → orderOf b = 2 → a ≠ b → a * b = b * a →
      GoodInvolution a → GoodInvolution b → GoodInvolution (a * b) →
        IsSporadic K .M12 ∧ ∃ h : K, h * a * h⁻¹ = b ∧ h * b * h⁻¹ = a * b

end CFSG.EvenSporadicStandard.HSStd
