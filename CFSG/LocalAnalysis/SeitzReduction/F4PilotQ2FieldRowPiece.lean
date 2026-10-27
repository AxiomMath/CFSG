module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.Quasithin (perfectCore)

section Piece

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem Q2FieldParam.subgroupToG_map_eq {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) (W₀ : Subgroup (N.levi (fixSubfield σ))) :
    subgroupToG e (W₀.map (N.levi (fixSubfield σ)).subtype) =
      ((W₀.map (leviInclusion σ N)).map h.Φ.toMonoidHom).map E.subtype := by
  ext g
  constructor
  · rintro ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    exact ⟨h.Φ (leviInclusion σ N w), ⟨_, ⟨w, hw, rfl⟩, rfl⟩, h.fix w⟩
  · rintro ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, (h.fix w).symm⟩

theorem Q2FieldParam.centralizerPerfectCore_sup_eq_map_levi {N : AmalgamNeighbour} {X : Subgroup G}
    (h : Q2FieldParam σ e N (centralizerPerfectCore X)) (W₀ : Subgroup (N.levi (fixSubfield σ))) :
    centralizerPerfectCore (X ⊔ subgroupToG e (W₀.map (N.levi (fixSubfield σ)).subtype)) =
      ((centralizerPerfectCore (W₀.map (leviInclusion σ N))).map h.Φ.toMonoidHom).map
        (centralizerPerfectCore X).subtype := by
  have := finite_levi K N
  have hW := h.subgroupToG_map_eq W₀
  have hWE : subgroupToG e (W₀.map (N.levi (fixSubfield σ)).subtype) ≤
      centralizerPerfectCore X := by
    rw [hW]
    exact map_subtype_le _
  have hsub : (((W₀.map (leviInclusion σ N)).map h.Φ.toMonoidHom).map
      (centralizerPerfectCore X).subtype).subgroupOf (centralizerPerfectCore X) =
        (W₀.map (leviInclusion σ N)).map h.Φ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (centralizerPerfectCore X).subtype_injective _
  rw [CFSG.SeitzReduction.F4Pilot.centralizerPerfectCore_sup_eq_map hWE, hW, hsub,
    map_centralizerPerfectCore h.Φ]

end Piece

end CFSG.SeitzReduction.F4Pilot
