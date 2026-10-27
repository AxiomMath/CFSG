module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.GH74.Uniqueness.SU.SU5A8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

@[expose] def GH73TheoremA64K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsKGroupCat X →
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ → CFSG.oddCore X = ⊥ → Subgroup.center X = ⊥ →
    (∃ S : Sylow 2 X, CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(S : Subgroup X)) →
    Nonempty (X ≃* alternatingGroup (Fin 8)) ∨ Nonempty (X ≃* alternatingGroup (Fin 9)) ∨
      Nat.card X = 960 ∨ Nat.card X = 1344 ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
        CFSG.Blueprint.LieModel X .PSp 2 p f

end CFSG.EvenSporadicStandard.HNRecog.GH73
