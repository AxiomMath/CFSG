module

public import Mathlib.GroupTheory.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG

variable (p : ℕ) (G : Type*) [Group G]

theorem pCore_eq_iSup :
    pCore p G = ⨆ (N : Subgroup G) (_ : N.Normal) (_ : IsPGroup p N), N := by
  unfold pCore
  rw [sSup_eq_iSup]
  apply le_antisymm
  · exact iSup₂_le fun N hN => le_iSup₂_of_le N hN.1 (le_iSup_of_le hN.2 le_rfl)
  · exact iSup₂_le fun N hN => iSup_le fun hN' => le_iSup₂_of_le N ⟨hN, hN'⟩ le_rfl

end CFSG
