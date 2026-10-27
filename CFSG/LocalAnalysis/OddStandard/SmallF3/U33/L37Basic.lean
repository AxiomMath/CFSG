module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

theorem pCore_eq_of_normal {Y : Type*} [Group Y] {p : ℕ} (N : Subgroup Y) [N.Normal]
    (hN : IsPGroup p N) (hmax : ∀ M : Subgroup Y, M.Normal → IsPGroup p M → M ≤ N) :
    CFSG.pCore p Y = N := by
  refine le_antisymm (hmax (CFSG.pCore p Y) CFSG.pCore_normal CFSG.pCore_isPGroup) ?_
  exact le_sSup ⟨inferInstance, hN⟩

variable {G G₁ : Type*} [Group G] [Group G₁]

end CFSG.OddStandard.SmallF3.HarrisU33
