module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def OddCoverAt {T : Type} [Group T] (Y : Subgroup T) (x : T) : Prop :=
  ∃ P R J : Subgroup T, IsTwoComponentIn P (centralizer ({x} : Set T)) ∧
    R ≤ centralizer ({x} : Set T) ∧ (R.subgroupOf (centralizer ({x} : Set T))).Normal ∧
    Odd (Nat.card R) ∧ J ≤ Y ⊓ centralizer ({x} : Set T) ∧ ⁅J, J⁆ = J ∧ P ≤ J ⊔ R ∧
    J ≤ P ⊔ R

@[expose] def SingleComponentSimpleAt (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T → ∀ X Y : Subgroup T,
    ⁅X, X⁆ = X → ⁅Y, Y⁆ = Y →
    IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) → IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) →
    2 ≤ CFSG.Open.pRank 2 X → 2 ≤ CFSG.Open.pRank 2 Y →
    ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y →
    (∀ x ∈ X, orderOf x = 2 → OddCoverAt Y x) → (∀ y ∈ Y, orderOf y = 2 → OddCoverAt X y) →
    False

end CFSG.ComponentClassification.Sol76.Sig
