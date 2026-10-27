module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenTC
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterAssembly
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Blueprint CFSG.Monster.Generated


theorem weakCoreClause_seven_of_monster {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) :
    ∀ S : Sylow 7 T, CFSG.Open.GLBWeakCore 7 (S : Subgroup T) = ⊤ ∨
      CFSG.AGLEmbedding.KlingenAlt 7 T S := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  exact fun S => CFSG.AGLEmbedding.weakCore_or_klingenAlt_of_mulEquiv ε
    weakCoreClause_seven_gmat S

theorem coverWeakGen_seven_of_monster {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : CFSG.AGLEmbedding.CoverWeakGen T 7 := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  exact CFSG.AGLEmbedding.Norton.OrdinaryProofs.coverWeakGen_of_mulEquiv ε
    coverWeakGen_seven_gmat

theorem sporCaseThreePrimeData_seven_of_monster {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : CFSG.AGLEmbedding.SporCaseThreePrimeData T 7 :=
  Or.inr (Or.inr ⟨weakCoreClause_seven_of_monster e, Or.inr (coverWeakGen_seven_of_monster e)⟩)

end CFSG.AGLEmbedding.Norton.MON5_7
