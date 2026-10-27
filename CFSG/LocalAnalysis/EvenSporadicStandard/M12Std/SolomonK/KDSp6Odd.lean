module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Blueprint

@[expose] def OddLieA12Sylow : Prop :=
  ∀ (F : Type) [Group F] [Finite F], OddLieType F →
    (∃ (S : Sylow 2 F) (S' : Sylow 2 (alternatingGroup (Fin 12))),
      Nonempty (↥(S : Subgroup F) ≃* ↥(S' : Subgroup (alternatingGroup (Fin 12))))) →
    ∀ E : Subgroup F, (∀ x ∈ E, x * x = 1) → Nat.card E = 2 ^ 6 →
      5 ∣ Nat.card (normalizer (E : Set F))

variable {K : Type} [Group K] [Finite K]

theorem false_of_odd_lie (hOdd : OddLieA12Sylow) (hK : SolomonA12HypK K) (h : OddLieType K) :
    False := by
  obtain ⟨E, hE⟩ := hK.exists_goodE
  have h5 := hOdd K h hK.sylowType E hE.sq hE.card
  rw [hE.card_normalizer] at h5
  norm_num at h5

end CFSG.EvenSporadicStandard.M12Std.SolomonK
