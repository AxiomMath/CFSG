module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.GroupTheory.SubgroupOfLattice
public import CFSG.CGT.PushingUpLit.BHS.GlaubRankOne

public section

namespace CFSG.GroupTheory

open CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem orbitClosure_subgroupOf_of_le {H Q T : Subgroup G} (hTH : T ≤ H)
    (hQt : ∀ t ∈ T, Q.map (MulAut.conj t).toMonoidHom ≤ H) :
    (orbitClosure Q T).subgroupOf H = orbitClosure (Q.subgroupOf H) (T.subgroupOf H) := by
  refine le_antisymm ?_ ?_
  · rw [orbitClosure]
    rw [CFSG.subgroupOf_iSup (fun t => ⨆ (_ : t ∈ T), Q.map (MulAut.conj t).toMonoidHom)
      (fun t => iSup_le fun ht => hQt t ht)]
    refine iSup_le fun t => ?_
    rw [CFSG.subgroupOf_iSup (fun (_ : t ∈ T) =>
      Q.map (MulAut.conj t).toMonoidHom) (fun ht => hQt t ht)]
    refine iSup_le fun ht => ?_
    rw [← CFSG.CGT.PushingUpLit.BHS.Glauberman.subgroupOf_map_conj (⟨t, hTH ht⟩ : ↥H)]
    exact le_iSup₂_of_le (⟨t, hTH ht⟩ : ↥H)
      (Subgroup.mem_subgroupOf.mpr ht) le_rfl
  · refine orbitClosure_le (X := Q.subgroupOf H) (A := T.subgroupOf H)
      (L := (orbitClosure Q T).subgroupOf H) fun u hu => ?_
    rw [CFSG.CGT.PushingUpLit.BHS.Glauberman.subgroupOf_map_conj u]
    exact Subgroup.subgroupOf_mono _
      (le_iSup₂_of_le (u : G) (Subgroup.mem_subgroupOf.mp hu) le_rfl)

end CFSG.GroupTheory
