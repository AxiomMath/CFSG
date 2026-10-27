module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.LieType.Steinberg.CentralExt

open CFSG.Open

variable {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)

@[expose] noncomputable def freeCongr : FreeGroup X ≃* FreeGroup Y :=
  FreeGroup.freeGroupCongr e.toEquiv

theorem lift_comp_freeCongr :
    (FreeGroup.lift id : FreeGroup Y →* Y).comp (freeCongr e).toMonoidHom =
      e.toMonoidHom.comp (FreeGroup.lift id) :=
  FreeGroup.ext_hom _ _ fun x => by simp [freeCongr]

theorem map_griessHopfRelations :
    (griessHopfRelations X).map (freeCongr e).toMonoidHom = griessHopfRelations Y := by
  ext y
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
  have h := DFunLike.congr_fun (lift_comp_freeCongr e) ((freeCongr e).symm y)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h
  rw [h, map_eq_one_iff e e.injective]

theorem map_commutator_freeGroup :
    (commutator (FreeGroup X)).map (freeCongr e).toMonoidHom = commutator (FreeGroup Y) := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective (freeCongr e).toMonoidHom (freeCongr e).surjective]

theorem map_bracket_griessHopfRelations :
    (⁅(⊤ : Subgroup (FreeGroup X)), griessHopfRelations X⁆).map (freeCongr e).toMonoidHom =
      ⁅(⊤ : Subgroup (FreeGroup Y)), griessHopfRelations Y⁆ := by
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective (freeCongr e).toMonoidHom (freeCongr e).surjective,
    map_griessHopfRelations]

@[expose] noncomputable def griessHopfMultiplierCongr :
    griessHopfMultiplier X ≃* griessHopfMultiplier Y := by
  have h1 : (griessHopfRelations X ⊓ commutator (FreeGroup X)).map (freeCongr e).toMonoidHom =
      griessHopfRelations Y ⊓ commutator (FreeGroup Y) := by
    rw [Subgroup.map_inf_eq _ _ (freeCongr e).toMonoidHom (freeCongr e).injective,
      map_griessHopfRelations, map_commutator_freeGroup]
  let e1 : ↥(griessHopfRelations X ⊓ commutator (FreeGroup X)) ≃*
      ↥(griessHopfRelations Y ⊓ commutator (FreeGroup Y)) :=
    ((freeCongr e).subgroupMap _).trans (MulEquiv.subgroupCongr h1)
  have he1 : ∀ r, ((e1 r : ↥(griessHopfRelations Y ⊓ commutator (FreeGroup Y))) :
      FreeGroup Y) = freeCongr e r := fun _ => rfl
  refine QuotientGroup.congr _ _ e1 ?_
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    change ((e1 x : ↥(griessHopfRelations Y ⊓ commutator (FreeGroup Y))) : FreeGroup Y) ∈ _
    rw [he1, ← map_bracket_griessHopfRelations e]
    exact Subgroup.mem_map_of_mem _ hx
  · intro hy
    rw [← map_bracket_griessHopfRelations e] at hy
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hy
    refine ⟨e1.symm y, ?_, e1.apply_symm_apply y⟩
    rw [Subgroup.mem_subgroupOf]
    have h := he1 (e1.symm y)
    rw [MulEquiv.apply_symm_apply, ← hwy] at h
    rw [(freeCongr e).injective h.symm]
    exact hw

end CFSG.LieType.Steinberg.CentralExt
