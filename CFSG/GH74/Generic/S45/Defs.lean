module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Orders.Sporadic
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.ABGLocalTools CFSG.Blueprint Subgroup

@[expose] def AutTwoInner (K : Type) [Group K] : Prop :=
  ∀ α : MulAut K, IsPGroup 2 ↥(zpowers α) → α ∈ (MulAut.conj : K →* MulAut K).range

@[expose] def KBase (K : Type) [Group K] [Finite K] : Prop :=
  IsSimpleGroup K ∧ AutTwoInner K ∧
    ∀ R : Sylow 2 K, (∀ a b : (R : Subgroup K), a * b = b * a) ∧
      (∀ a : (R : Subgroup K), a * a = 1) ∧ Nat.card (R : Subgroup K) = 8 ∧
      Nat.card ↥(normalizer ((R : Subgroup K) : Set K)) =
        21 * Nat.card ↥(centralizer ((R : Subgroup K) : Set K))

@[expose] def IsJ1OrRee (K : Type) [Group K] : Prop :=
  NativeSporadic.IsSporadic K .J1 ∨ ∃ f : ℕ, LieModel K .twistedG2 0 3 f

@[expose] def B_S45_KFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsJ1OrRee K → KBase K

end CFSG.GH74.Generic.S45
