module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.SectionRank.QTK

open Subgroup

@[expose] def J4ListInspect : Prop :=
  ∀ (S : Type) [Group S] [Finite S], QTKSimpleList S →
    ∀ (L : Type) [Group L] [Finite L] (j : L →* S), Function.Injective j →
      ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ → ∀ (Q : Subgroup L) [Q.Normal], IsPGroup 2 Q →
        CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q) → ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥ →
          Nonempty (S ≃* CFSG.RankThree.PartTwo.Sec4.Spor .J4)

end CFSG.SectionRank.QTK
