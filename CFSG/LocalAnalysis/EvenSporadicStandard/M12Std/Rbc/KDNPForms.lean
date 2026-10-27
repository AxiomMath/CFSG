module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup) in
@[expose] def KDNPSmall : Prop :=
  ∀ (E : Type) [Group E] [Finite E], CFSG.IsQuasisimple E → IsPGroup 2 (center E) →
    ∀ σ : MulAut E, orderOf σ = 2 → IsPGroup 2 (fixedSubgroup σ) →
      Nat.card (fixedSubgroup σ) ≤ 4 →
        Nonempty (E ⧸ center E ≃* alternatingGroup (Fin 5)) ∧ Nat.card (fixedSubgroup σ) = 4

@[expose] def KDNPEight : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ → ∀ t : E, orderOf t = 2 →
    (∀ a ∈ centralizer ({t} : Set E), ∀ b ∈ centralizer ({t} : Set E), a * b = b * a) →
    Nat.card (centralizer ({t} : Set E)) = 8 →
    ∀ A : Subgroup E, Nonempty (↥A ≃* alternatingGroup (Fin 5)) → False

end CFSG.EvenSporadicStandard.M12Std.Rbc
