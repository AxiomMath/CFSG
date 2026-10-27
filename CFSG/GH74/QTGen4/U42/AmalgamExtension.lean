module

public import CFSG.GH74.QTGen4.U42.GSidePairDataExt
public import CFSG.GH74.QTGen4.U42.ModelExtCore
public import CFSG.GH74.QTGen4.U42.AmalgamPlain
public import CFSG.GH74.QTGen4.U42.ModelExtLatticeC

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut


theorem model_U_extension_iff
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (he : ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g)
    (g : ↥P2h) : (g : Ah) ∈ pCoreOf 2 P1h ↔ ((e g : Mof _) : Mc) ∈ U0 := by
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hmap : ((pCoreOf 2 P1h).subgroupOf P2h).map φ = U0 := map_pCoreOf_P1h_aligned e he
  constructor
  · intro hg
    have h := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hg)
    rwa [hmap] at h
  · intro hg
    have h : φ g ∈ U0 := hg
    rw [← hmap] at h
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp h
    exact Subgroup.mem_subgroupOf.mp (hφ hug ▸ hu)

variable {G : Type} [Group G] [Finite G] {T' L V H I : Subgroup G}

theorem amalgam_iso_extension (S : A5.Setting G T' L V) (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hE : ¬ Setting.PlainCase S) :
    Nonempty ((RankTwoAmalgam.ofSubgroups H (L ⊔ T')).Iso
      (RankTwoAmalgam.ofSubgroups P1h P2h)) := by
  obtain ⟨e, he, hU, hB, hT, hUB⟩ := pairData_extension S hH D hE
  obtain ⟨eY, _, heR⟩ := exists_model_coords_aligned
  have hBY : ∀ g : ↥P2h, (g : Ah) ∈ P1h ↔ ((eY g : Mof _) : Mc) ∈ Bhc := by
    intro g
    have h : (g : Ah) ∈ P1h ↔ (g : Ah) ∈ Bh :=
      ⟨fun hg => ⟨hg, g.2⟩, fun hg => hg.1⟩
    rw [h, model_Bh_aligned_iff]
    change extAlignedPerm g 4 = 4 ↔ ((eY g : Mof _) : Mc).right 4 = 4
    rw [heR]
  have hTY : ∀ g : ↥P2h, (g : Ah) ∈ That ↔ ((eY g : Mof _) : Mc) ∈ Thc := by
    intro g
    rw [model_That_aligned_iff]
    change InD (extAlignedPerm g) ↔ InD ((eY g : Mof _) : Mc).right
    rw [heR]
  have hU0 : U0 ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    fun _ _ => mem_Mof.mpr (Subgroup.mem_top _)
  exact amalgam_iso_of_coords hU0 e eY hB hBY hT hTY hU
    (model_U_extension_iff eY heR) (pairCore_extension S hH D hE)
    model_pairCore_extension hUB

theorem amalgam_U42_extension (S : A5.Setting G T' L V) (hH : H ∈ S.Hz)
    (D : Data13515 S H I) (hE : ¬ Setting.PlainCase S) :
    IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups H (L ⊔ T')) := by
  refine ⟨Y, inferInstance, Ah, inferInstance, incl, lieModel_Y, incl_injective, ?_,
    That, P1h, P2h, ModelExtLatticeC.isYAmalgamPair_Ah, amalgam_iso_extension S hH D hE⟩
  rw [← Yh_eq_range]
  exact index_Yh

theorem amalgam_U42_constructive (S : A5.Setting G T' L V) (hH : H ∈ S.Hz)
    (D : Data13515 S H I) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H (L ⊔ T')) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups H (L ⊔ T')) := by
  classical
  by_cases hP : Setting.PlainCase S
  · exact Or.inl (amalgam_U42_plain S hH D hP)
  · exact Or.inr (amalgam_U42_extension S hH D hP)

end CFSG.GH74.QTGen4.U42
