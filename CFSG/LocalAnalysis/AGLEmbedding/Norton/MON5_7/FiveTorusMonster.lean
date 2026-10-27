module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FiveTorus
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Sporadic.Co2Cert.Order

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Blueprint CFSG.AGLEmbedding CFSG.Open


theorem nonempty_torusDatum_five_of_monster {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : Nonempty (TorusDatumP 5 T (Fin 15)) := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  obtain ⟨D⟩ := nonempty_torusDatum_gmat_five
  exact ⟨D.ofMulEquiv ε.symm⟩

theorem tcGenDatum_five_of_monster {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : TCGenDatum T 5 := by
  obtain ⟨D⟩ := nonempty_torusDatum_five_of_monster e
  exact D.tcGenDatum (by norm_num) (by norm_num)

theorem weakCore_five_of_monster {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) (S : Sylow 5 T) :
    GLBWeakCore 5 (S : Subgroup T) = ⊤ :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  weakCoreOfTC T 5 (tcGenDatum_five_of_monster e) S

theorem weakCoreClause_five_of_monster {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) :
    ∀ S : Sylow 5 T, GLBWeakCore 5 (S : Subgroup T) = ⊤ ∨ KlingenAlt 5 T S :=
  fun S => Or.inl (weakCore_five_of_monster e S)

theorem liftableNormalizerGen_five_of_monster {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : LiftableNormalizerGenP 5 T := by
  obtain ⟨D⟩ := nonempty_torusDatum_five_of_monster e
  exact D.liftableNormalizerGenP (by norm_num) (by norm_num)

theorem coverWeakGen_five_of_monster {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) [Fact (Nat.Prime 5)] : CoverWeakGen T 5 :=
  coverWeakGen_of_liftableP (by norm_num) (liftableNormalizerGen_five_of_monster e)

end CFSG.AGLEmbedding.Norton.MON5_7
