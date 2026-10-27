module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup

@[expose] def HSJ3TwoMultiplierFact : Prop :=
  (∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → IsPGroup 2 ↥(center Y) →
      Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.HS) → Nat.card ↥(center Y) ≤ 2) ∧
    ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → IsPGroup 2 ↥(center Y) →
      Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.J3) → center Y = ⊥

@[expose] def TwoHSTwoBFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y →
    Nonempty (Y ⧸ center Y ≃* Blueprint.NativeSporadic.HS) → Nat.card ↥(center Y) = 2 →
    ∀ τ : MulAut Y, orderOf τ = 2 → τ ∈ innAut Y →
    ∀ K : Subgroup Y, IsTwoComponentIn K (fixedPoints τ) →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 3 2 →
      Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
        Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6)))

end CFSG.ComponentClassification.HarrisLit.N36
