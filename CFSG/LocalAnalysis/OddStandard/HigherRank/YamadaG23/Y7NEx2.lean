module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NEx1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y7n_nonsplit_of_sub {N F : Subgroup G} (hFN : F ≤ N) (hF : IsE 3 ↥F)
    (hq : SecProp N F (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))))
    (hns : ¬ SplitsOver N F) :
    ¬ SplitsOver (⊤ : Subgroup ↥N) (pCoreOf 2 (⊤ : Subgroup ↥N)) := by
  rintro ⟨C, -, hinf, hsup⟩
  have hpcore : pCoreOf 2 (⊤ : Subgroup ↥N) = F.subgroupOf N := y7n_pcore_eq hFN hF hq
  refine hns ⟨C.map N.subtype, map_subtype_le C, ?_, ?_⟩
  · have h1 : F ⊓ C.map N.subtype = (pCoreOf 2 (⊤ : Subgroup ↥N) ⊓ C).map N.subtype := by
      rw [Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, hpcore,
        map_subgroupOf_eq_of_le hFN]
    rw [h1, hinf, Subgroup.map_bot N.subtype]
  · have h2 : F ⊔ C.map N.subtype = (pCoreOf 2 (⊤ : Subgroup ↥N) ⊔ C).map N.subtype := by
      rw [Subgroup.map_sup, hpcore, map_subgroupOf_eq_of_le hFN]
    rw [h2, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.OddStandard.HigherRank.YamadaG23
