module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

theorem alternatingGroup_fin_eight_not_comm :
    ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin 8)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h8 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 8)).mp this
  simp at h8

theorem isSimpleGroup_and_not_comm_of_mulEquiv_alt8 {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 8)) : IsSimpleGroup H ∧ ∃ a b : H, a * b ≠ b * a := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := alternatingGroup_fin_eight_not_comm
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.EvenSporadicStandard.M24Std
