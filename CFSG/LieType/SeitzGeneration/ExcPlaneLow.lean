module

public import CFSG.LieType.SeitzGeneration.ExcPlaneUntw
public import CFSG.LieType.SeitzGeneration.ExcPlaneSplit
public import CFSG.LieType.HighestRoot.CentChevalleyData

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.HighestRoot
  CFSG.TauCetiBridge TauCeti


theorem excPlaneF4Low : ExcPlaneF4Low := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hdvd⟩ hr
  exact exists_plane_untwisted_levi (c := LieTypeIndex.F4) Even.chevalleyBridgesAll.f4
    (fun _ => LieTypeIndex.characteristic_F4 _) noG2_F4 (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
    (k := ⟨1, by decide⟩) (l := ⟨3, by decide⟩) (by decide) (by decide) symmetrizer_le_F4
    (by decide) (by decide)
    (fun h => by
      have := h ▸ Set.mem_univ (⟨1, by decide⟩ : Fin (Tag.rank .F4))
      simp [Fin.ext_iff] at this) q hv hp hp2 hdvd

theorem excPlaneE6Low : ExcPlaneE6Low := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hdvd⟩ hr
  exact exists_plane_untwisted_levi (c := LieTypeIndex.E6) Even.chevalleyBridgesAll.e6
    (fun _ => LieTypeIndex.characteristic_E6 _) noG2_E6' (i := ⟨0, by decide⟩)
    (j := ⟨1, by decide⟩) (k := ⟨2, by decide⟩) (l := ⟨3, by decide⟩) (by decide) (by decide)
    (symmetrizer_le_one .E6 rfl _) (by decide) (by decide)
    (fun h => by
      have := h ▸ Set.mem_univ (⟨2, by decide⟩ : Fin (Tag.rank .E6))
      simp [Fin.ext_iff] at this) q hv hp hp2 hdvd

theorem excPlaneE7Low : ExcPlaneE7Low := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hdvd⟩ hr
  exact exists_plane_untwisted_levi (c := LieTypeIndex.E7) Even.chevalleyBridgesAll.e7
    (fun _ => LieTypeIndex.characteristic_E7 _) noG2_E7' (i := ⟨0, by decide⟩)
    (j := ⟨1, by decide⟩) (k := ⟨2, by decide⟩) (l := ⟨3, by decide⟩) (by decide) (by decide)
    (symmetrizer_le_one .E7 rfl _) (by decide) (by decide)
    (fun h => by
      have := h ▸ Set.mem_univ (⟨2, by decide⟩ : Fin (Tag.rank .E7))
      simp [Fin.ext_iff] at this) q hv hp hp2 hdvd

theorem excPlaneE8Low : ExcPlaneE8Low := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hdvd⟩ hr
  exact exists_plane_untwisted_levi (c := LieTypeIndex.E8) Even.chevalleyBridgesAll.e8
    (fun _ => LieTypeIndex.characteristic_E8 _) noG2_E8 (i := ⟨0, by decide⟩)
    (j := ⟨1, by decide⟩) (k := ⟨2, by decide⟩) (l := ⟨3, by decide⟩) (by decide) (by decide)
    (symmetrizer_le_one .E8 rfl _) (by decide) (by decide)
    (fun h => by
      have := h ▸ Set.mem_univ (⟨2, by decide⟩ : Fin (Tag.rank .E8))
      simp [Fin.ext_iff] at this) q hv hp hp2 hdvd

end CFSG.LieType.SeitzGeneration
