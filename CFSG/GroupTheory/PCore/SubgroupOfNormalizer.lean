module

public import CFSG.Open.LocalVocabulary
public import CFSG.Foundations.Basic
import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic

public section

namespace CFSG.GroupTheory

open CFSG.Open

theorem map_subtype_pCoreOf_normalizer_subgroupOf {G : Type*} [Group G] (p : ℕ)
    {X T : Subgroup G} (hTX : T ≤ X) :
    (pCoreOf p (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X))).map X.subtype =
      CFSG.inSubgroup (CFSG.pCore p) (X ⊓ Subgroup.normalizer (T : Set G)) := by
  rw [← CFSG.ASVolI.ChH.pCoreOf_map_of_injective p X.subtype X.subtype_injective,
    ← Subgroup.subgroupOf_normalizer_eq hTX, Subgroup.subgroupOf_map_subtype,
    inf_comm (Subgroup.normalizer (T : Set G)) X]
  rfl

end CFSG.GroupTheory
