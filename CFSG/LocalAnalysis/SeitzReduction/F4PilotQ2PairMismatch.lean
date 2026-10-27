module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem subgroupToG_map_conj (e : L ≃* adjointGroup .F4 K) (W : Subgroup (adjointGroup .F4 K))
    (m : adjointGroup .F4 K) :
    subgroupToG e (W.map (MulAut.conj m).toMonoidHom) =
      (subgroupToG e W).map (MulAut.conj ((e.symm m : L) : G)).toMonoidHom := by
  unfold subgroupToG
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem subgroupToG_trans_symm (e : L ≃* adjointGroup .F4 K) (ψ : MulAut (adjointGroup .F4 K))
    (W : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (e.trans ψ.symm) W = subgroupToG e (W.map ψ.toMonoidHom) := by
  unfold subgroupToG
  congr 1
  rw [Subgroup.map_map]
  rfl

theorem card_centralizerPerfectCore_subgroupToG_map_conj [Finite G] (e : L ≃* adjointGroup .F4 K)
    (W : Subgroup (adjointGroup .F4 K)) (m : adjointGroup .F4 K) :
    Nat.card (centralizerPerfectCore (subgroupToG e (W.map (MulAut.conj m).toMonoidHom))) =
      Nat.card (centralizerPerfectCore (subgroupToG e W)) := by
  rw [subgroupToG_map_conj, ← map_centralizerPerfectCore]
  exact Subgroup.card_map_of_injective (MulAut.conj ((e.symm m : L) : G)).injective

end Transport

end CFSG.SeitzReduction.F4Pilot
