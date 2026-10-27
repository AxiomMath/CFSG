module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def TypC (K : Type) [Group K] : Prop :=
  Blueprint.OddLieType (K ⧸ Open.fusionZStar K) ∨
    (∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (K ⧸ pPrimeCore 2 K) n) ∨
    (GH74.GLS.IsL34Quotient (K ⧸ pPrimeCore 2 K) ∧
      ¬ IsElementaryAbelian 2 ↥(center (K ⧸ pPrimeCore 2 K)))

@[expose] def TypPumpInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SectionRank.IsKGroupCat Y → HarrisLit.IsTwoQuasisimple Y →
    center (Y ⧸ pPrimeCore 2 Y) ≠ ⊥ →
    ∀ β : MulAut Y, (∀ y, β (β y) = y) →
    ∀ T : Subgroup Y, T ≤ fixedSubgroup β → IsPComponent 2 (T.subgroupOf (fixedSubgroup β)) →
      center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥ → TypC ↥T → TypC Y

@[expose] def TypPumpLeaf (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → pPrimeCore 2 Y = ⊥ → center Y ≠ ⊥ →
    P Y → ∀ β : MulAut Y, (∀ y, β (β y) = y) →
    ∀ T : Subgroup Y, T ≤ fixedSubgroup β → IsPComponent 2 (T.subgroupOf (fixedSubgroup β)) →
      center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥ → TypC ↥T → False

@[expose] def TypLeafSpor (Y : Type) [Group Y] : Prop :=
  Blueprint.NativeSporadic.SporadicRep (Y ⧸ center Y)

@[expose] def TypLeafEven (Y : Type) [Group Y] : Prop :=
  Blueprint.EvenLieType (Y ⧸ center Y) ∧ ¬ Blueprint.OddLieType (Y ⧸ center Y) ∧
    (∀ n : ℕ, IsEmpty (Y ⧸ center Y ≃* alternatingGroup (Fin n))) ∧
    ¬ (GH74.GLS.IsL34Quotient Y ∧ ¬ IsElementaryAbelian 2 ↥(center Y))

@[expose] def TypQ (q₀ : ℕ) (K : Type) [Group K] : Prop :=
  (Blueprint.OddLieType (K ⧸ Open.fusionZStar K) ∨
      ∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (K ⧸ pPrimeCore 2 K) n) ∧
    q₀ * (q₀ ^ 2 - 1) ∣ Nat.card (K ⧸ pPrimeCore 2 K)

@[expose] def TypL16 (K : Type) [Group K] : Prop :=
  GH74.GLS.IsL34Quotient (K ⧸ pPrimeCore 2 K) ∧ Nat.card ↥(center (K ⧸ pPrimeCore 2 K)) = 16

end CFSG.ComponentClassification.GS82PumpInputs
