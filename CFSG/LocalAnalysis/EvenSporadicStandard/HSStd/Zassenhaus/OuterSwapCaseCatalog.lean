module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd

@[expose] def KGA8Q8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Catalog K → IsSimpleGroup K →
    ∀ τ : MulAut K, τ * τ = 1 → τ ≠ 1 → Nat.card (autCentralizer τ) ≤ 161280 →
    (∃ D : Subgroup ↥(autCentralizer τ), D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧
        ∀ x : ↥(autCentralizer τ), ∃ n : ℕ, x ^ (2 ^ n) ∈ D) →
      PumpType K ∧
        (Nonempty (K ≃* alternatingGroup (Fin 10)) ∨ Nonempty (K ≃* alternatingGroup (Fin 12)) ∨
          IsSporadic K .HS ∨ Nat.card K = 987033600) ∧
        (IsSporadic K .HS → τ ∉ (MulAut.conj : K →* MulAut K).range)

@[expose] def KGA8CoverElem : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 8)) →
      ∃ E : Subgroup K, (∀ x ∈ E, x * x = 1) ∧ 4 < Nat.card E

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
