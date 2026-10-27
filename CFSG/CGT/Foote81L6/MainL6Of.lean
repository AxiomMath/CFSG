module

public import CFSG.CGT.Foote81L6.MainAbstract
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitFooteMain

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

@[expose] def FooteL6Bridge : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Sylow 2 H),
    (∃ (p f : ℕ) (L : Type) (_ : Group L), p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧
      CFSG.Blueprint.LieModel L .PSL 6 p f ∧ ∃ P : Sylow 2 L, Nonempty (↥S ≃* ↥P)) →
    ∃ z : H, (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = zpowers z ∧
      orderOf z = 2 ∧ ∃ (m n : ℕ) (D : FooteData (centralizerQuot z) (sylowQuot S z) m n),
        LiftsSquareToZ S z D.toFooteCore

theorem footeMainL6_of
    (hB : FooteL6Bridge) (h1 : FooteTheorem1) :
    CFSG.OddStandard.HigherRank.YamadaG23.FooteMainL6 := by
  intro H _ _ S hS
  obtain ⟨z, hZ, hz2, m, n, D, hl⟩ := hB H S hS
  exact ⟨z, hZ, footeMainAbstract_of_theorem1 h1 H S z hZ hz2 m n D hl⟩

end CFSG.CGT.Foote81L6
