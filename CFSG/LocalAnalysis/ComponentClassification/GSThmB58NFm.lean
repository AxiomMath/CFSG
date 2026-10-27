module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def EvenAltPumpUp : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ E : Subgroup H, IsPGroup 2 E → E ≤ normalizer (M : Set H) →
      (∀ e ∈ E, e ^ 2 ∈ coreActionKernel M) →
      Nat.card E ≤ 4 * Nat.card ↥(E ⊓ coreActionKernel M) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer (E : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer (E : Set H))) →
      Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 10)) →
      (∃ n : ℕ, 10 ≤ n ∧ Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) ∨
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN)

end CFSG.ComponentClassification.GSThmB
