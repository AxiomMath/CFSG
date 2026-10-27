module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped Pointwise

section Sylow

variable {K : Type} [Field K]

theorem exists_sylow_eq_posUnipotent [Finite K] [CharP K 2] :
    ∃ S : Sylow 2 (adjointGroup .F4 K), (S : Subgroup (adjointGroup .F4 K)) =
      (posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .F4) (K := K)) (card_posUnipotent (τ := .F4) (K := K))
  exact ⟨hUp.toSylow hUi, IsPGroup.toSylow_coe hUp hUi⟩

end Sylow

end CFSG.SeitzReduction.F4Pilot
